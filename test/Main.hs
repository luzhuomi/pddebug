import Text.Regex.PDeriv.Debug.Refine9

import qualified Data.ByteString.Char8 as S

g = [(1::Int, Pair 0 (anyNum 90) (Star 0 (anyNum 90)))]

sw = S.pack w'

main :: IO ()
main = -- print $ test g ".*<span>([0-9]*)</span>.*" sw
  print $ test g "a" (S.pack "abc")
