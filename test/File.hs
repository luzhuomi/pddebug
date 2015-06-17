import Text.Regex.PDeriv.Debug.Refine6
import System.Environment

g = [(1::Int, Pair 0 (anyNum 90) (Star 0 (anyNum 90)))]

main :: IO ()
main = do 
  (filename:args) <- getArgs
  file <- readFile filename
  print $ test g ".*<span>([0-9]*)</span>.*" file