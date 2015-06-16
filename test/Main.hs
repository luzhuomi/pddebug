import Text.Regex.PDeriv.Debug.Refine5


g = [(1::Int, Pair 0 (anyNum 90) (Star 0 (anyNum 90)))]

main :: IO ()
main = print $ test g ".*<span>([0-9]*)</span>.*" w'