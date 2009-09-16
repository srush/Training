{-# LANGUAGE TypeSynonymInstances, TypeFamilies, FlexibleInstances #-}
module TAG where 
import Control.Monad (liftM, ap)
import Sentence
import DependencyStructure
import Test.QuickCheck
import ArbitraryHelpers
import Data.Char (toUpper)
import Data.List
import Data.Maybe (fromJust)
import Data.Monoid
import NLP.Semiring
import NLP.Semiring.Derivation
import NLP.FSM.Simple
import NLP.Probability.ConditionalDistribution
import NLP.ChartParse
import NLP.ChartParse.Eisner
import Debug.Trace
import Debug.Trace.Helpers

import qualified Data.Map as M

newtype NonTerm = NonTerm String 
          deriving (Eq, Ord)

instance Show NonTerm where 
    show (NonTerm nt) = nt

instance Arbitrary NonTerm where
    arbitrary = 
      NonTerm `liftM` map toUpper `liftM` listOf1 (elements alpha) 
  
newtype Spine = Spine [NonTerm]
           deriving (Eq, Ord)

top (Spine (nt:_)) = Just nt
top (Spine []) = Nothing

getNonTerm i (Spine nts) = nts !! i

type TAGWord = (GWord, Spine)

instance Context GWord where 
    type Sub (GWord) = String
    decompose (Word word, POS pos) = [pos, word] 
    compose [pos, word] = (Word word, POS pos)


type Distance = (Bool) -- TODO : this make this more accurate
type AdjunctionContext = (NonTerm, Distance, POS, Word)

-- this is lame, but need it to make subcontext type safe
data AdjunctionSub = AdjunctionSub {
      adjNonTerm :: Maybe NonTerm,
      adjDistance:: Maybe Distance,
      adjPOS :: Maybe POS,
      adjWord :: Maybe Word }
                     deriving (Eq, Ord)

instance Show AdjunctionSub where 
    show a = concatMap (\f-> f a) 
             [maybeShow . adjNonTerm, 
              maybeShow. adjDistance,
              maybeShow. adjPOS, 
              maybeShow. adjWord]  
        where maybeShow Nothing = ""
              maybeShow (Just m) = show m ++ " " 

adjSubDef = AdjunctionSub Nothing Nothing Nothing Nothing

instance Context AdjunctionContext where
    type Sub (AdjunctionContext) = AdjunctionSub
    decompose (nonterm, dis, pos, word) = [adjSubDef {adjNonTerm =Just nonterm,
                                                      adjDistance = Just dis},
                                           adjSubDef {adjPOS = Just pos},
                                           adjSubDef {adjWord = Just word}]
    compose [adjSub1,adjSub2,adjSub3] =  (fromJust $ adjNonTerm adjSub1, 
                                          fromJust $ adjDistance adjSub1,
                                          fromJust $ adjPOS adjSub2,  
                                          fromJust $ adjWord adjSub3) 

newtype TAGTrainingCounts = TAGTrainingCounts 
    (CondObserved Spine GWord, -- pick the spine 
     CondObserved (GWord, Maybe NonTerm) AdjunctionContext) 
    deriving (Eq, Ord)

instance Show TAGTrainingCounts where 
    show (TAGTrainingCounts (a,b)) = "\n \t\t" ++ (show a) ++ "\n \t\t" ++ (show b)

type TAGCountSemi = Derivation TAGTrainingCounts 

instance Monoid TAGTrainingCounts  where 
    mempty = TAGTrainingCounts (mempty, mempty)
    mappend (TAGTrainingCounts (a,b)) (TAGTrainingCounts (a', b')) = 
        TAGTrainingCounts (mappend a a', mappend b b')

mkTagWords words = 
    mkSentence $ map (\ (word,spine) -> 
                      (mkDerivation $ 
                       TAGTrainingCounts (singletonObservation spine word, mempty), 
                       (word, spine))) words


instance Arbitrary Spine where
    arbitrary = Spine `liftM` listOf1 arbitrary

instance WordSym TAGWord where
    root = (root, Spine [NonTerm "ROOT"])

instance Show Spine where 
    show (Spine nts) = intercalate "+" $ ["*"] ++ map show nts

data TAGSentence semi = TAGSentence (Sentence semi (GWord, Spine)) (Dependency Int)
                      deriving (Show)
instance (Arbitrary (TAGSentence TAGCountSemi)) where 
    arbitrary = do
      sent <- listOf1 arbitrary
      let tsent = mkTagWords sent 
      dep <- arbDepMap (sentenceLength tsent) (pickAdjInd tsent)
      return $ TAGSentence tsent dep
          where pickAdjInd sent i = do 
                  let (_, Spine sp) = getWord sent i
                  choose (0,length sp -1)

directCounts (TAGSentence sent dep) =
    TAGTrainingCounts (spineCounts, adjCounts) 
        where
          adjCounts = 
              mconcat $
              map (\(i, DEdge j info) -> 
                       mkAdjunction (getWord sent j) (getWord sent i) (j, DEdge i info)) $ 
              map (\i -> (i, getHead dep i)) [1..n]
          spineCounts = 
              mconcat $ 
              map (\((word), spine) -> 
                       singletonObservation spine word) $ 
              map (getWord sent) [1..n]
          n = sentenceLength sent

type TAGFSM semi = GraphWFSM Int (GWord, Spine) semi
type GetSemi word edge semi =  word -> word -> (Int, DEdge edge)  -> semi


tagSentenceFSMs :: (Semiring semi) =>  
    TAGSentence semi ->  GetSemi (GWord, Spine) (Int) semi ->
    [(TAGFSM semi, TAGFSM semi)]     
tagSentenceFSMs (TAGSentence sent dep) mkSemi = 
    map (\(i, e) -> makeDependencyFSM (getWord sent) mkSemi i e) $
    flattenDep dep

mkTagDepDerivation :: GetSemi TAGWord Int TAGCountSemi
mkTagDepDerivation w1 w2 edge  =
    mkDerivation $ TAGTrainingCounts 
                     (mempty,
                      mkAdjunction w1 w2 edge 
                     ) -- w

mkAdjunction ((headWord, headPos), headSpine)  (childWord, childSpine) (head, DEdge child pos )  =
    singletonObservation (childWord, -- r 
                          top childSpine) -- R,  
                             (getNonTerm pos headSpine, -- H
                              abs (head -child) == 1, -- delta
                              headPos, --t
                              headWord)
    
prop_directCheck tagsent = --trace ((show finalSemi) ++ "\n\n" ++ (show $ directCounts tagsent))  $  
    (directCounts tagsent == fromDerivation finalSemi)
    where types = tagsent:: (TAGSentence (Derivation TAGTrainingCounts)) 
          (TAGSentence sent _) = tagsent 
          fsms = tagSentenceFSMs tagsent mkTagDepDerivation
          getFSM i word = fsms !! (i-1)
          (Just finalSemi, _) = eisnerParse getFSM sent
