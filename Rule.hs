{-# LANGUAGE TypeFamilies #-}
module Rule where
import qualified ProofTree as PT
import qualified Prop as P
import qualified Terms as T
import Controller
import Unification
import Miso.String (MisoString, pack)
import Optics.Core
import StringRep
import Control.Monad(when)
import Data.Maybe(fromMaybe)

data Rule = R PT.RuleName P.Prop (Maybe ProofState) deriving (Show, Eq)

type Counter = Int
data ProofState = PS PT.ProofTree Counter deriving (Show, Eq)

name :: Lens' Rule PT.RuleName
name = lensVL $ \act (R n prp m) -> (\n' -> R n' prp m) <$> act n


blankAxiom :: PT.RuleName -> Rule
blankAxiom n = (R n P.blank Nothing)

blankTheorem :: PT.RuleName -> Rule
blankTheorem n = (R n P.blank (Just $ PS (PT.fromProp P.blank) 0))

-- warning, do not use this lens to assign to anything that might invalidate the proof state
-- use propUpdate for that (which will reset the proof state)
prop :: Lens' Rule P.Prop
prop = lensVL $ \act (R n prp m) -> (\prp' -> R n prp' m) <$> act prp

-- disjoint product of prop and name
namedProp :: Lens' Rule PT.NamedProp
namedProp = lensVL $ \act (R n prp m) -> (\(PT.Defn n',prp') -> R n' prp' m) <$> act (PT.Defn n, prp)

propUpdate :: Setter' Rule P.Prop
propUpdate = sets guts
  where
    guts act (R n p s) 
      | p' <- act p
      = R n p' (fmap (const $ PS (PT.fromProp p') 0) s)

proofState :: AffineTraversal' Rule ProofState
proofState =  atraversal
  (\i   -> case i of R _ _ (Just s) -> Right s
                     i -> Left i)
  (\i s -> case i of R n p (Just _) -> R n p (Just s)
                     i -> i)

unresolved :: ProofState -> Bool
unresolved (PS pt c) = has PT.outstandingGoals pt

proofTree :: Lens' ProofState PT.ProofTree
proofTree = lensVL $ \act (PS pt c) -> flip PS c <$> act pt   

runUnifyPS :: (PT.ProofTree -> UnifyM PT.ProofTree) -> ProofState -> Either UnifyError ProofState
runUnifyPS act (PS pt c) = case runUnifyM (act pt) c of
                             (Left e, c) -> Left e
                             (Right pt',c') -> Right (PS pt' c')

checkVariableName :: String -> Controller (Focus Rule) ()
checkVariableName new = case T.invalidName new of 
  Just e  -> errorMessage $ "Invalid variable name: "  ++ e
  Nothing -> pure ()

instance Control Rule where 
  data Focus Rule = GoalFocus PT.Path
                  | ProofBinderFocus PT.Path Int 
                  | RuleBinderFocus P.Path Int 
                  | NewRuleBinderFocus P.Path 
                  | RuleTermFocus P.Path 
                  | NameFocus
                  deriving (Show, Eq)

  data Action Rule = Apply PT.NamedProp PT.Path
                   | Nix PT.Path
                   | RenameProofBinder PT.Path Int
                   | AddRuleBinder P.Path
                   | RenameRuleBinder P.Path Int
                   | DeleteRuleBinder P.Path Int
                   | UpdateTerm P.Path
                   | AddPremise P.Path
                   | DeletePremise P.Path
                   | Rename
                   deriving (Show, Eq)

  defined (R n _ _) = [n]

  inserted _ = RuleTermFocus []

  invalidated s r = over (proofState % proofTree) (PT.clear s) r

  renamed (s,s') r = over (proofState % proofTree) (PT.renameRule (s,s')) r 

  editable (ProofBinderFocus pth i) = fmap pack . preview (proofState % proofTree % PT.path pth % PT.goalbinders % ix i)
  editable (RuleBinderFocus pth i) = fmap pack . preview (prop % P.path pth % P.metabinders % ix i)
  editable (RuleTermFocus pth) = Just . pack . P.getConclusionString pth . view prop
  editable NameFocus = fmap pack . preview name
  editable _ = const Nothing
  
  
  leaveFocus (ProofBinderFocus p i) = noFocus . handle (RenameProofBinder p i)
  leaveFocus (RuleBinderFocus p i)  = noFocus . handle (RenameRuleBinder p i)
  leaveFocus (NewRuleBinderFocus p) = noFocus . handle (AddRuleBinder p)
  leaveFocus (RuleTermFocus p)      = noFocus . handle (UpdateTerm p)
  leaveFocus NameFocus              = noFocus . handle Rename
  leaveFocus _                      = pure
  
  handle (Apply np pth) state = case traverseOf proofState (runUnifyPS $ PT.apply np pth) state of 
     Left e -> errorMessage e >> pure state 
     Right state' -> let
          newFocus = if has (proofState % proofTree % PT.path (0:pth)) state'
                     then Just (0:pth)
                     else fst <$> ipreview (isingular (proofState % proofTree % PT.outstandingGoals)) state'
        in do
          case newFocus of 
            Just f -> setFocus (GoalFocus f)
            _      -> clearFocus
          pure state'
  
  handle (Nix pth) state = do
     clearFocus
     pure $ set (proofState % proofTree % PT.path pth % PT.step) Nothing state
  
  handle (RenameProofBinder pth i) state = do
     new <- textInput
     checkVariableName new
     clearFocus -- should it be updateterm?
     pure $ set (proofState % proofTree % PT.path pth % PT.goalbinders % ix i) new state 
  
  handle (AddRuleBinder pth) state = do
     new <- textInput
     checkVariableName new
     invalidate (view name state)
     setFocus (RuleTermFocus pth)
     pure $ over (propUpdate % P.path pth) (P.addBinder new) state 
  
  handle (RenameRuleBinder pth i) state = do
     new <- textInput
     checkVariableName new
     clearFocus -- should it be updateterm?
     pure $ set (prop % P.path pth % P.metabinders % ix i) new state 
  
  handle (DeleteRuleBinder pth i) state = do
     new <- textInput
     checkVariableName new
     when (maybe False (P.isBinderUsed i) $ preview (prop % P.path pth) state) $ errorMessage "Cannot remove binder: is in use"
     invalidate (view name state)
     clearFocus
     pure $ over (propUpdate % P.path pth) (P.removeBinder i) state 
  
  handle (UpdateTerm pth) state = do
     new <- textInput
     case toLensVL prop (P.setConclusionString pth new) state of
       Left e -> errorMessage $ "Parse error: " ++ e
       Right state' -> do
         invalidate (view name state')
         case pth of [] -> clearFocus
                     (_:pth') -> setFocus (RuleTermFocus pth')
         pure $ over propUpdate id state' --hack..
  
  handle (AddPremise pth) state = do
     invalidate (view name state)
     let newIndex = length $ fromMaybe [] (preview (prop % P.path pth % P.premises) state)
     setFocusWithLeaving (RuleTermFocus (newIndex:pth))
     pure $ over (propUpdate % P.path pth % P.premises) (++[P.blank]) state
  
  handle (DeletePremise []) state = pure state -- shouldn't happen
  handle (DeletePremise (x:pth)) state = do
     invalidate (view name state)
     setFocus (RuleTermFocus (pth))
     pure $ over (propUpdate % P.path pth) (P.removePremise x) state
  
  handle Rename state = do
     new <- textInput
     when (new == "") $ errorMessage "Name cannot be empty"
     renameResource (view name state) new
     clearFocus
     pure $ set name new state
