import Text.Regex.PDeriv.Debug.Refine10
import System.Environment
import qualified Data.ByteString.Char8 as S


g = [(1::Int, Pair 0 (Any 90) (Star 0 (Any 90)))]

main :: IO ()
main = do 
  (filename:args) <- getArgs
  file <- S.readFile filename
  print $ test2 g ".*<h1 class=\"header-gray\">[\n\r]*([a-zA-Z;&, \\\n\t\r]*)</h1>.*" file
  -- print $ test2 g ".*aa(b*)aa.*" (S.pack "cabac")
