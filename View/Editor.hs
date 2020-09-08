{-# LANGUAGE OverloadedStrings #-}
module View.Editor where
import Miso
import qualified Miso.String as MS
import Editor
import qualified Heading as H
import qualified Item as I
import qualified Paragraph as P
import qualified Rule as R
import qualified Terms as T
import View.Item
import View.Term
import View.Prop
import View.Utils hiding (LocalAction (..))

viewEditor :: Editor -> View EditorAction
viewEditor x =
  div_ [class_ "container", onKeyDown (\(KeyCode kc) -> if kc == 27 then Reset else Noop)] $
    [ div_ [class_ "document", id_ "document"] 
      $ renderDoc (inputText x) (displayOptions x) (currentFocus x) (document x) ++ [block "document-endofcontent" []]
    , div_ [class_ "sidebar", id_ "sidebar"] 
      $ logo
      : maybe id (\m -> (block "sidebar-errormessage" [text m] :)) (message x)
        [ block "sidebar-main" mainSidebar
        , renderDisplayOptions (displayOptions x)
        ]
    , script_ [] "Split(['#document','#sidebar'],{ sizes: [70,30], minSize:200});"
    ]
  where
    mainSidebar = case currentFocus x of
      ItemFocus i (I.RuleFocus (R.GoalFocus p)) ->
        let (ctx, rs) = rulesSummary (i, p) (document x)
         in concatMap (renderPropGroup i p ctx) rs
      NewItemFocus i -> newItemMenu i
      ItemFocus i (I.ParagraphFocus _) -> editingHelp
      CreditsFocus ->
        [ block "sidebar-header" ["Credits"]
        , block "sidebar-credits"
          [ "Holbert is made by "
          , a_ [href_ "http://liamoc.net"] ["Liam O'Connor"]
          , ", a lecturer at the University of Edinburgh,"
          , "using GHCJS and the Miso framework. Some icons are from the Typicons icon set by Stephen Hutchings."
          , " It (will be) released under the BSD3 license."
          , " Some code is based on work by Daniel Gratzer and Tobias Nipkow."
          ]
        ]
      _ -> [block "sidebar-header" ["Facts Summary:"], renderIndex $ document x]

    renderPropGroup i p ctx (n, rs) =
      [ block "sidebar-header" [text $ MS.pack (n ++ ":")]
      , block "sidebar-apply-group" $ map (renderAvailableRule ctx (displayOptions x) (i, p)) rs
      ]

    logo = div_ [class_ "sidebar-logo", onClick (SetFocus CreditsFocus)]
                [small_ [] ["click for credits"], inline "logo-text" ["Holbert"], space, "0.1"]

    newItemMenu i = let insertHeading i n = InsertItem i (I.Heading (H.Heading n "")) in
      [ block "sidebar-header" ["Proof elements:"]
      , button "sidebar-insert" (SetFocus $ InsertingPropositionFocus False i) [block "item-rule-theoremheading" ["Axiom."]]
      , button "sidebar-insert" (SetFocus $ InsertingPropositionFocus True i) [block "item-rule-theoremheading" ["Theorem."]]
      , block "sidebar-header" ["Text elements:"]
      , button "sidebar-insert" (insertHeading i 1) [h2_ [] ["Heading 1"]]
      , button "sidebar-insert" (insertHeading i 2) [h3_ [] ["Heading 2"]]
      , button "sidebar-insert" (insertHeading i 3) [h4_ [] ["Heading 3"]]
      , button "sidebar-insert" (insertHeading i 4) [h5_ [] ["Heading 4"]]
      , button "sidebar-insert" (InsertItem i (I.Paragraph $ P.Paragraph "")) [block "sidebar-insert-paragraph" ["Paragraph"]]
      ]
    editingHelp =
      [ block "sidebar-header" ["Editing Help"]
      , table_ [class_ "sidebar-paragraph-editing"]
        [ tr_ []
          [ td_ [class_ "sidebar-paragraph-editing-lhs"] [code_ [] ["~codeSnippet()~"]]
          , td_ [] [code_ [] ["codeSnippet()"]]
          ]
        , tr_ []
          [ td_ [class_ "sidebar-paragraph-editing-lhs"] [code_ [] ["*bold text*"]]
          , td_ [] [b_ [] ["bold text"]]
          ]
        , tr_ []
          [ td_ [class_ "sidebar-paragraph-editing-lhs"] [code_ [] ["/italic text/"]]
          , td_ [] [i_ [] ["italic text"]]
          ]
        , tr_ []
          [ td_ [class_ "sidebar-paragraph-editing-lhs"] [code_ [] ["$_/\\_ A B$"]]
          , td_ [class_ "inline-math"] [renderTerm (TDO True True) $ T.Ap (T.Ap (T.Const "_/\\_") (T.Const "A")) (T.Const "B")]
          ]
        , tr_ []
          [ td_ [class_ "sidebar-paragraph-editing-lhs"] [code_ [] ["$A B:_/\\_ A B$"]]
          , td_ [class_ "inline-math"] $ pure $ renderTermCtx ["A", "B"] (TDO True True) (T.Ap (T.Ap (T.Const "_/\\_") (T.LocalVar 1)) (T.LocalVar 0))
          ]
        ]
      ]

renderIndex (_ : script) = ul_ [class_ "sidebar-index"] $ renderIndex' (zip [1 ..] script)
  where
    renderIndex' ((i, I.Heading (H.Heading lvl hd)) : scr)
      | (itms, rest) <- span (within lvl) scr =
        li_ [] [b_ [] [a_ [href_ $ "#anchor" <> (MS.pack $ show i)] [text hd]], ul_ [] $ renderIndex' itms] : renderIndex' rest
    renderIndex' ((i, I.Rule (R.R n _ mpt)) : scr) =
      li_ []
        [ a_ [href_ $ "#anchor" <> (MS.pack $ show i)] [definedrule n]
        , case mpt of
            Just ps
              | R.unresolved ps -> inline "sidebar-index-unsolved" [typicon "warning"]
              | otherwise -> inline "sidebar-index-solved" [typicon "input-checked"]
            Nothing -> span_ [] []
        ]
      : renderIndex' scr
    renderIndex' ((i, _) : scr) = renderIndex' scr
    renderIndex' [] = []
    within n (_, I.Heading (H.Heading lvl hd)) = lvl > n
    within n _ = True

renderDoc textIn opts selected script = zipWith go [0 ..] script
  where
    scriptSize = length script
    go i item =
      let mainItem = renderItem opts i textIn item selected
          inserting = selected == NewItemFocus i
          itemOptions
            | i > 0 =
              block "item-options" 
                $  [button "button-icon button-icon-red" (DeleteItem i) [typicon "trash"]]
                ++ (if i > 1              then [button "button-icon button-icon-teal" (ShiftDown $ i -1) [typicon "arrow-up-outline"]] else [])
                ++ (if i < scriptSize - 1 then [button "button-icon button-icon-teal" (ShiftDown i) [typicon "arrow-down-outline"]] else [])
            | otherwise = ""
          insertButton =
            let (cls, icn) = if inserting
                  then ("button-icon button-icon-insert button-icon-active", "plus")
                  else ("button-icon button-icon-insert button-icon-blue", "plus-outline")
             in button cls (SetFocus $ NewItemFocus i) [typicon icn]
                  : case selected of
                    InsertingPropositionFocus isT i' | i == i' ->
                      [editorWithTitle (if isT then theoremHeading i else axiomHeading i) "newrule" (InsertProposition i isT) UpdateInput Reset textIn]
                    _ -> []
       in block (if inserting then "item item-inserting" else "item") $ [mainItem, itemOptions] ++ insertButton

renderAvailableRule ctx opts (i, p) (rr, r) =
  button "apply-option" (ItemAction (Just i) $ I.RuleAct $ R.Apply (rr, r) p) 
    [fmap (const Noop) $ renderPropName (Just rr) ctx ruleDOs r]
  where
    ruleDOs = RDO {termDisplayOptions = tDOs opts, showInitialMetas = showMetaBinders opts, ruleStyle = compactRules opts}

renderDisplayOptions opts =
  form_ [class_ "sidebar-displayoptions"]
    [ div_ [class_ "sidebar-header"] ["Rule Format:"]
    , input_ [checked_ (compactRules opts == Turnstile), id_ "linear", type_ "radio", name_ "rules", onChecked (\_ -> ChangeDisplayOptions (opts {compactRules = Turnstile}))]
    , label_ [for_ "linear"] ["Linear"]
    , input_ [checked_ (compactRules opts == Bar), id_ "vertical", type_ "radio", name_ "rules", onChecked (\_ -> ChangeDisplayOptions (opts {compactRules = Bar}))]
    , label_ [for_ "vertical"] ["Vertical"]
    , input_ [checked_ (compactRules opts == BarTurnstile), id_ "mixture", type_ "radio", name_ "rules", onChecked (\_ -> ChangeDisplayOptions (opts {compactRules = BarTurnstile}))]
    , label_ [for_ "mixture"] ["Hybrid"]
    , div_ [class_ "sidebar-header"] ["Proof Tree Contexts:"]
    , input_ [checked_ (assumptionsMode opts == Hidden), type_ "radio", name_ "assumptions", id_ "assH", onChecked (\_ -> ChangeDisplayOptions (opts {assumptionsMode = Hidden}))]
    , label_ [for_ "assH"] ["Hidden"]
    , input_ [checked_ (assumptionsMode opts == New), type_ "radio", name_ "assumptions", id_ "assN", onChecked (\_ -> ChangeDisplayOptions (opts {assumptionsMode = New}))]
    , label_ [for_ "assN"] ["New Only"]
    , input_ [checked_ (assumptionsMode opts == Cumulative), type_ "radio", name_ "assumptions", id_ "assC", onChecked (\_ -> ChangeDisplayOptions (opts {assumptionsMode = Cumulative}))]
    , label_ [for_ "assC"] ["All"]
    , div_ [class_ "sidebar-header"] ["Display Options:"]
    , div_ []
        [ input_ [checked_ (showMetaBinders opts), id_ "showMB", type_ "checkbox", onChecked (\(Checked b) -> ChangeDisplayOptions (opts {showMetaBinders = b}))]
        , label_ [for_ "showMB"] ["Show Quantifiers"]
        ]
    , div_ []
        [ input_ [checked_ (showTeles (tDOs opts)), id_ "showTeles", type_ "checkbox", onChecked (\(Checked b) -> ChangeDisplayOptions (opts {tDOs = (tDOs opts) {showTeles = b}}))]
        , label_ [for_ "showTeles"] ["Show Metavariable Telescopes"]
        ]
    , div_ []
        [ input_ [checked_ (showInfixes (tDOs opts)), id_ "useInfix", type_ "checkbox", onChecked (\(Checked b) -> ChangeDisplayOptions (opts {tDOs = (tDOs opts) {showInfixes = b}}))]
        ,  label_ [for_ "useInfix"] ["Use Infix Notation"]
        ]
    ]