import Text.Regex.PDeriv.Debug.Refine9
import System.Environment
import qualified Data.ByteString.Char8 as S


g = [(1::Int, Pair 0 (Any 90) (Star 0 (Any 90)))]

main :: IO ()
main = do 
  (filename:args) <- getArgs
  file <- S.readFile filename
  print $ test g ".*<h1 class=\"header-gray\">\n([a-zA-Z\n]*)</h1>.*" file
