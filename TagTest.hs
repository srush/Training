import TAG
import TreeBank
import Sentence 
import Data.Array
import NLP.ChartParse.Eisner
import Debug.Trace.Helpers
import Debug.Trace
main = do 
  sent <- readSentence "data/sample2.data"
  let dsent = toTAGDependency sent
  let (TAGSentence sent _) = dsent
  print sent
  let fsms = tagSentenceFSMs dsent mkTagDepDerivation
  let getFSM i word = fsms !! (i-1)
  return $ eisnerParse getFSM sent