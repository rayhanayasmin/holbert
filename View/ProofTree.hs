{-# LANGUAGE OverloadedStrings #-}
module View.ProofTree where
import Miso
import qualified Miso.String as MS
import Data.List (intersperse)
import Data.Maybe (isNothing, isJust, fromMaybe)
import DisplayOptions
import qualified Item as I
import qualified Rule as R
import qualified Prop as P
import qualified Terms as T
import ProofTree
import View.Prop
import View.Utils
import View.Term
import View.Paragraph (renderText)


renderProofTree opts pt tbl selected textIn = renderPT False False [] [] [] pt
  where
    
    termDOs = tDOs opts
    ruleDOs = RDO {termDisplayOptions = termDOs, showInitialMetas = True, ruleStyle = Turnstile}
    renderRR (P.Rewrite r fl) = span_ [class_ "rule-rulename-rewrite"]  [renderRR r, sup_ [] [if not fl then "→" else "←"]]
    renderRR (P.Elim r i) = span_ [class_ "rule-rulename-elim"] [renderRR r, sup_ [] [renderRR i]]
    renderRR (P.Defn d) = definedrule d
    renderRR (P.Local i) = localrule i
    renderRR (P.Transitivity) = "trans"

    currentGS = case selected of 
      Just (R.ProofFocus t g) -> g 
      _ -> Nothing

    renderPT inTree showPreamble rns ctx pth (PT ptopts sks lcls prp msgs) =
      let binders = (if showMetaBinders opts && not showPreamble then concat (zipWith (metabinder' pth) [0 ..] sks) else [])
                 ++ boundrules
          boundrules = if assumptionsMode opts == Hidden && not showPreamble then map rulebinder [length rns .. length rns + length lcls - 1] else []       
          premises = case msgs of
            Just (rr, sgs) -> zipWith (renderPT (inTree || (shouldBeStyle /= Prose)) (isJust ptopts) rns' ctx') (map (: pth) [0 ..]) sgs
            Nothing        -> []
          spacer = maybe (goalButton pth) (const $ "") msgs

          ruleTitle = Just $ maybe "?" (addNix . renderRR . fst) msgs


          subtitleWidget = case selected of
              Just (R.ProofFocus (R.SubtitleFocus pth') _) | pth == pth' -> editor "expanding" (R.SetSubgoalHeading pth) txt  
              _ -> button "editable editable-heading" "" (SetFocus (R.ProofFocus (R.SubtitleFocus pth) currentGS)) (renderText tbl txt)
            where txt = case ptopts of Nothing -> "Show:"; Just opts -> subtitle opts


          wordboundrules [] [] = []
          wordboundrules [] [(lab,c)] = [div_ []  [ span_ [class_ "item-rule-proofheading"] ["Assuming "], renderRR lab, ": ",renderPropNameE (InProofTree (selected,textIn)) Nothing ctx' ruleDOs c ]]
          wordboundrules [] ls = [div_ [class_ "item-rule-proofheading"] ["Assuming:"], ul_ [] (map (\(lab,c)-> li_ [] [renderRR lab, ": ", renderPropNameE (InProofTree (selected,textIn)) Nothing ctx' ruleDOs c]) ls)]
          wordboundrules vars [] = [div_ []  [ span_ [class_ "item-rule-proofheading"] ("Given " : concat (zipWith (metabinder' pth) [0 ..] vars)) ]]
          wordboundrules vars [(lab,c)] = [div_ []  [ span_ [class_ "item-rule-proofheading"] ("Given " : concat (zipWith (metabinder' pth) [0 ..] vars)), span_ [class_ "item-rule-proofheading"] [" where "], renderRR lab, ": ",renderPropNameE (InProofTree (selected,textIn)) Nothing ctx' ruleDOs c ]]
          wordboundrules vars ls = [div_ []  [ span_ [class_ "item-rule-proofheading"] ("Given " : concat (zipWith (metabinder' pth) [0 ..] vars)), span_ [class_ "item-rule-proofheading"] [" where:"], ul_ [] (map (\(lab,c)-> li_ [] [renderRR lab, ": ", renderPropNameE (InProofTree (selected,textIn)) Nothing ctx' ruleDOs c]) ls)]]
          preamble = div_ [class_ "word-proof-prop"] 
            $ (div_ [class_ "proof-subtitle"] [multi (wordboundrules (if showMetaBinders opts then sks else []) $ zip (map P.Local [length rns ..]) lcls)] :)
            $ (div_ [] [subtitleWidget]:)
            $ [div_ [class_ "word-proof-goal"] [ renderPropNameE (InProofTree (selected, textIn)) Nothing ctx' ruleDOs $ P.Forall [] [] prp ] ]

          conclusion = pure $ renderPropNameLabelledE (Just $ case assumptionsMode opts of
              New | not showPreamble -> map P.Local [length rns ..]
              Cumulative | not showPreamble -> map P.Local [0..]
              _ -> []) Nothing (InProofTree (selected, textIn)) Nothing ctx' ruleDOs
                           $ P.Forall [] (case assumptionsMode opts of
              New  | not showPreamble -> lcls
              Cumulative | not showPreamble -> rns'
              _ -> []) prp
       in if (shouldBeStyle == Equational) then
            multi $ (if inTree || not showPreamble then id else (preamble:) )                
                  $ (if inTree || showPreamble then id else (span_ [class_ "item-rule-proofheading"] ["Proof. " ] :) )
                  $ (if inTree || not showPreamble then id else ("by: ":))
                  $ (if inTree then id else (styleButton :))
                  $ (if inTree then id else (equationalButton :))
                  $ pure $ (table_ 
                    [ intProp "cellpadding" 2, class_ "equational-proof",intProp "cellspacing" 2]
                    ([ tr_ []
                      $  [td_ [class_ "rule-cell rule-binderbox"] [renderTermCtxEditable (Just (textIn, flip R.ProofFocus currentGS . R.MetavariableFocus, R.InstantiateMetavariable, selected)) ctx (tDOs opts) a1]]
                      ++ [td_ [class_ "rule-cell rule-spacer"] ["  "]]
                      ++ [td_ [class_ "rule-cell rule-rulebox"] ["   "]]
                      ++  [td_ [class_ "rule-cell rule-empty"] [" "]]
                      ++  [td_ [class_ "rule-cell rule-empty"] [" "]]
                    ] ++ (concatMap (renderEqPT ctx') bs)))
          else if shouldShowWords then 
            multi $ (if showPreamble then id else (span_ [class_ "item-rule-proofheading"] ["Proof. "] :) )
                  $ (preamble:)
                  $ (multi [" by ", fromMaybe "" ruleTitle, spacer, if null premises then ". " else ": "]  :)
                  $ (styleButton :)
                  $ pure $ wordsrule premises 
          else 
            multi $ (if inTree || not showPreamble then id else (preamble:) )                
                  $ (if inTree || showPreamble then id else (span_ [class_ "item-rule-proofheading"] ["Proof. " ] :) )
                  $ (if inTree || not showPreamble then id else ("by: ":))
                  $ (if inTree then id else (styleButton :))
                  $ (if inTree then id else (equationalButton :))
                  $ pure $ inferrule binders premises spacer ruleTitle conclusion

      where
        (a1, bs) = flatten (PT ptopts sks lcls prp msgs) pth
        wordsrule [p] =  div_ [class_ "word-proof"] [p]
        wordsrule premises =
          div_ [class_ "word-proof"] [ ul_ [] $ map (li_ [] . pure) premises ]
        styleButton = if shouldShowWords then 
                        iconButton "grey" "Switch to tree style" "tree" (Act $ R.ToggleStyle pth)
                      else 
                        iconButton "grey" "Switch to prose style" "flow-children" (Act $ R.ToggleStyle pth)
        equationalButton = if (shouldBeStyle == Tree || shouldBeStyle == Prose) && True then
                        iconButton "grey" "Switch to equational style" "equals" (Act $ R.ToggleEquational pth)
                      else if (shouldBeStyle == Equational)  then
                        iconButton "grey" "Switch to tree style" "tree" (Act $ R.ToggleEquational pth)
                      else
                        button_ [class_ "button-icon button-icon-grey", type_ "button", title_ "Cannot apply equational style"] [typicon "equals-outline"]
                        
        shouldShowWords = notTree && not (shouldBeStyle == Equational)
        notTree = not inTree && not (shouldBeStyle == Tree)
        shouldBeStyle = case ptopts of Nothing -> Tree; Just opts -> proofStyle opts
        isTransitive = case msgs of
          Just (P.Transitivity, sgs) -> True
          _ -> False
        addNix t = multi [t, iconButton "red" "Delete proof subtree" "trash" (Act $ R.Nix pth)]

        rulebinder v = multi [localrule v, miniTurnstile]

        rns' = map (P.raise (length sks)) rns ++ lcls
        ctx' = reverse sks ++ ctx
    
    renderEqPT :: [T.Name] -> (T.Term, (Maybe (P.RuleRef, [ProofTree])), Path) -> [View (LocalAction (R.Focus R.Rule) (R.Action R.Rule))]
    renderEqPT ctx (g, pt, pth) = case pt of
      Just (rr, pts) -> [tr_ []
                      $  [td_ [class_ "rule-cell rule-empty"] [" "]]
                      ++ [td_ [class_ "rule-cell rule-equals"] [" = "]]
                      ++ [td_ [class_ "rule-cell rule_term"] [renderTermCtxEditable (Just (textIn, flip R.ProofFocus currentGS . R.MetavariableFocus, R.InstantiateMetavariable, selected)) ctx (tDOs opts) g]]
                      ++ [td_ [class_ "rule-cell rule_ref"] [inline "" [renderRR rr, iconButton "red" "Delete sub-equality" "trash" (Act $ R.Nix pth)]]]]

      Nothing -> [tr_ []
                      $  [td_ [class_ "rule-cell rule-empty"] [" "]]
                      ++ [td_ [class_ "rule-cell rule-equals"] [" = "]]
                      ++ [td_ [class_ "rule-cell rule_term"] [renderTermCtxEditable (Just (textIn, flip R.ProofFocus currentGS . R.MetavariableFocus, R.InstantiateMetavariable, selected)) ctx (tDOs opts) g]]
                      ++ [td_ [class_ "rule-cell rule_ref"] [inline "" [spacer, iconButton "red" "Delete sub-equality" "trash" (Act $ R.Nix (drop 1 pth))]]]]

      where
        spacer = maybe (goalButton pth) (const $ "") pt


    metabinder' pth i n = case selected of
      Just (R.ProofFocus (R.ProofBinderFocus pth' i') _) | pth == pth', i == i' -> [metabinderEditor pth i textIn]
      _ -> [button "editable editable-math" "" (SetFocus $ R.ProofFocus (R.ProofBinderFocus pth i) currentGS) [metabinder n]]

    metabinderEditor pth i n = editor "expanding" (R.RenameProofBinder pth i) n

    goalButton pth  = case selected of
      Just (R.ProofFocus _ (Just (R.GS _ _ _ pth' _)))  | pth == pth' -> focusedButton "button-icon button-icon-active button-icon-goal" "" (Act $ R.SelectGoal pth) [typicon "location"]
      _ -> button "button-icon button-icon-blue button-icon-goal" "Unsolved goal" (Act $ R.SelectGoal pth) [typicon "location-outline"]



flatten :: ProofTree -> Path -> (T.Term, [(T.Term, (Maybe (P.RuleRef, [ProofTree])), Path)])
flatten (PT opts sks lcls (T.Ap (T.Const "_=_") (T.Ap g1 g2)) (Just (P.Transitivity, [a,b]))) pth = (g1, as++bs) where
  as = flattenTail a (0:pth)
  bs = flattenTail b (1:pth)
flatten (PT opts sks lcls (T.Ap (T.Ap (T.Const "_=_") g1) g2) (Just (P.Transitivity, [a,b]))) pth = (g1, as++bs) where
  as = flattenTail a (0:pth)
  bs = flattenTail b (1:pth)
flatten (PT opts sks lcls (T.Ap (T.Const "_=_") (T.Ap g1 g2)) (Just (rr, mgs))) pth = (g1, [(g2, (Just (rr, mgs)),(0:pth))]) 
flatten (PT opts sks lcls (T.Ap (T.Ap (T.Const "_=_") g1) g2) (Just (rr, mgs))) pth = (g1, [(g2, (Just (rr, mgs)),(0:pth))])
flatten (PT opts sks lcls (T.Ap (T.Const "_=_") (T.Ap g1 g2)) (Nothing)) pth = (g1, [(g2, (Nothing),(0:pth))])
flatten (PT opts sks lcls (T.Ap (T.Ap (T.Const "_=_") g1) g2) (Nothing)) pth = (g1, [(g2, (Nothing),(0:pth))])
flatten (PT opts sks lcls g mgs) pth = (g, [])


flattenTail :: ProofTree -> Path -> [(T.Term, (Maybe (P.RuleRef, [ProofTree])), Path)]
flattenTail (PT opts sks lcls g (Just (P.Transitivity, [a,b]))) pth = as++bs where
  as = flattenTail a (0:pth)
  bs = flattenTail b (1:pth)

flattenTail (PT opts sks lcls (T.Ap (T.Const "_=_") (T.Ap g1 g2)) mgs) pth = [(g2, mgs, pth)]
flattenTail (PT opts sks lcls (T.Ap (T.Ap (T.Const "_=_") g1) g2) mgs) pth = [(g2, mgs, pth)]
flattenTail (PT opts sks lcls g mgs) pth = []

{-flatten :: ProofTree -> [T.Term]
flatten pt = renderTransitive (map extract (proofTreeList pt))

proofTreeList :: ProofTree -> [ProofTree]
proofTreeList (PT opts sks lcls g (Just (P.Transitivity, [a,b]))) = concatMap proofTreeList [a,b]
proofTreeList (PT opts sks lcls g mgs) = [(PT opts sks lcls g Nothing)]

extract :: ProofTree -> T.Term
extract (PT opts sks lcls g mgs) = g

renderTransitive :: [T.Term] -> [T.Term]
renderTransitive (x:xs) = takeBoth x ++ concatMap takeSecond xs where
  takeBoth :: T.Term -> [T.Term]
  takeBoth (T.Ap (T.Const "_=_") (T.Ap a b)) = [a,b]
  takeBoth (T.Ap (T.Ap (T.Const "_=_") a) b) = [a,b]
  takeBoth _ = []

  takeSecond :: T.Term -> [T.Term]
  takeSecond (T.Ap (T.Const "_=_") (T.Ap a b)) = [b]
  takeSecond (T.Ap (T.Ap (T.Const "_=_") a) b) = [b]
  takeSecond _ = []-}
