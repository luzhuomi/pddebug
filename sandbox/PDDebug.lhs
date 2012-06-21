

includes now ordering on environment

> {-# LANGUAGE GADTs, FlexibleInstances, BangPatterns #-} 

--------------------------------------------------------------------------------
-- Regular Expression Pattern Matching via Derivatives
--------------------------------------------------------------------------------

> module Main where

> import Monad
> import List 
> import Data.Bits
> import Data.Char (ord)
> import GHC.IO
> import GHC.Int
> import qualified Data.IntMap as IM
> import qualified Data.ByteString.Char8 as S

> import System.IO.Unsafe

------------------------------
-- regular expressions

> data RE where
>   Phi :: RE                      -- empty language
>   Empty :: RE                    -- empty word
>   L :: Char -> Int -> RE                -- single letter with a position number
>   Choice :: RE  -> RE  -> RE     -- r1 + r2
>   Seq :: RE  -> RE  -> RE        -- (r1,r2)
>   Star :: RE  -> RE              -- r*
>  deriving Eq

A word is a byte string.

> type Word = S.ByteString

Pretty printing of regular expressions

> instance Show RE where
>     show Phi = "{}"
>     show Empty = "<>"
>     show (L c i) = show c ++ show i
>     show (Choice r1 r2) = ("(" ++ show r1 ++ "|" ++ show r2 ++ ")")
>     show (Seq r1 r2) = ("<" ++ show r1 ++ "," ++ show r2 ++ ">")
>     show (Star r) = (show r ++ "*")



annotate add position info to the regex

> newtype State s a = State { runState :: (s -> (a,s)) } 
 
> instance Monad (State s) where
>    -- return :: a -> State s a
>    return a        = State (\s -> (a,s))
>    -- (>>=) :: State s a -> (a -> State s b) -> State s b
>    (State x) >>= f = State (\s -> let (a,s') = x s 
>                                       stb = f a
>                                   in (runState stb) s')

> run :: s -> State s a -> (a,s)
> run s sta = (runState sta) s


> data CounterEnv = CounterEnv { cnt :: Int
>                              } deriving Show

> initEnv :: CounterEnv 
> initEnv = CounterEnv 0 

> nextCounter :: State CounterEnv Int
> nextCounter = State (\env -> let c = (cnt env) + 1
>                                  env' = c `seq` env{cnt=c}
>                              in env' `seq` (c, env'))


annotate a regex with position index

> rAnnotate :: RE -> RE
> rAnnotate r = case run initEnv (rAnn r) of
>              { (r', _ ) -> r' }  

> rAnn :: RE -> State CounterEnv RE
> rAnn Phi = return Phi
> rAnn Empty = return Empty
> rAnn (Choice r1 r2) = 
>   do { r1' <- rAnn r1
>      ; r2' <- rAnn r2
>      ; return (Choice r1' r2') }
> rAnn (Seq r1 r2) = 
>   do { r1' <- rAnn r1
>      ; r2' <- rAnn r2
>      ; return (Seq r1' r2') }
> rAnn (Star r) = 
>   do { r' <- rAnn r                
>      ; return (Star r') }
> rAnn (L c _) = 
>   do { i <- nextCounter       
>      ; return (L c i) }



> resToRE :: [RE] -> RE
> resToRE (r:res) = foldl Choice r res
> resToRE [] = Phi


> sigmaRE :: RE -> [Char]
> sigmaRE (L l _) = [l]
> sigmaRE (Seq r1 r2) = nub ((sigmaRE r1) ++ (sigmaRE r2))
> sigmaRE (Choice r1 r2) = nub ((sigmaRE r1) ++ (sigmaRE r2))
> sigmaRE (Star r) = sigmaRE r
> sigmaRE Phi = []
> sigmaRE Empty = []

> class IsEmpty a where
>     isEmpty :: a -> Bool

> instance IsEmpty RE where
>   isEmpty Phi = False
>   isEmpty Empty = True
>   isEmpty (Choice r1 r2) = (isEmpty r1) || (isEmpty r2)
>   isEmpty (Seq r1 r2) = (isEmpty r1) && (isEmpty r2)
>   isEmpty (Star r) = True
>   isEmpty (L _ _) = False

> type Loc = Int

> 

> data Tree a = Leaf 
>              | Single a (Tree a) 
>              | Branch a (Tree a) (Tree a) deriving Show 

> newtype DMonad h a = DMonad { runDM :: h -> (a, h) }

> instance Monad (DMonad s) where
>    return a = DMonad (\h -> (a,h) )
>    (DMonad x) >>= f = DMonad (\h -> let (a, h') = x h 
>                                     in runDM (f a) h')



> addLocM :: Loc -> DMonad [Loc] ()
> addLocM loc = DMonad (\h -> ((),h++[loc])) -- todo


> derivM :: RE -> Char -> DMonad [Loc] RE
> derivM Phi l = return Phi
> derivM Empty l = return Phi
> derivM (L l' loc) l | l == l' = addLocM loc >> return Empty
>                     | otherwise = return Phi
> derivM (Seq r1 r2) l 
>  | isEmpty r1 = do 
>       { r1' <- derivM r1 l
>       ; r2' <- derivM r2 l                 
>       ; return (Choice (Seq r1' r2) r2')
>       } 
>  | otherwise = do  
>       { r1' <- derivM r1 l
>       ; return (Seq r1' r2)
>       }
> derivM (Choice r1 r2) l = 
>  do { r1' <- derivM r1 l 
>     ; r2' <- derivM r2 l 
>     ; return (Choice r1' r2') } 
> derivM (Star r) l = do 
>  { r' <- derivM r l
>  ; return (Seq r' (Star r))
>  }

> {-

> append :: Tree Loc -> Tree Loc -> Tree Loc
> append Leaf t = t -- root case
> append (Single j t) t' = Single j (append t t')
> append (Branch _ _ _) _ = error "append:error"

> branch :: Tree Loc -> Tree Loc -> Tree Loc -> Tree Loc 
> branch Leaf t1 t2 = Branch 0 t1 t2 -- root case
> branch (Single j t) t1 t2 = Single j (Branch t t1 t2)

> derivS ::  Tree Loc -> RE -> Char ->  (Tree Loc, RE)
> derivS t Phi l = (t, Phi)                        
> derivS t Empty l = (t, Phi)
> derivS t (L l loc) l' | l == l' = (append t (Single loc Leaf), Empty)
>                       | otherwise = (Leaf, Phi)
> derivS t (Choice r1 r2) l = 
>    let (t1',r1') = derivS t1 r1 l
>        (t2',r2') = derivS t2 r2 l          
>    in (branch Leaf i t1' t2', Choice r1' r2')
> derivS t (Seq r1 r2) l 
>    | isEmpty r1 = 
>      let (t1,r1') = derivS r1 l   
>          (t2,r2') = derivS r2 l 
>      in (branch t t1 t2, Choice (Seq r1' r2) r2')
>    | otherwise =
>      let (t1,r1') = derivS r1 l
>      in (branch t i t1, Seq r1' r2)
> derivS (Star r) l = 
>    let (t',r') = derivS t r l
>    in (t', Seq r' (Star r))


> -}

runDM  (do { r1' <- derivM  (rAnnotate r1) 'A' ; r1'' <- derivM r1' 'A' ; derivM r1'' 'A' }) []
           


> pderivT :: [(RE, [Loc])] -> Char -> [(RE, [Loc])]
> pderivT rs c = nub2 $ concatMap (\r -> pdT r c) rs

> pdT :: (RE, [Loc]) -> Char -> [(RE, [Loc])]
> pdT (Phi, locs) c = []
> pdT (Empty, locs) c = []
> pdT (L l loc, locs) c | l == c = [(Empty, locs ++ [loc])]
>                       | otherwise = []
> pdT (Seq r1 r2, locs) c 
>   | isEmpty r1 = ([ (Seq r1' r2, locs') | (r1',locs') <- pdT (r1,locs) c ] ++ (pdT (r2,locs) c))
>   | otherwise  = [ (Seq r1' r2, locs') | (r1',locs') <- pdT (r1,locs) c ]
> pdT (Choice r1 r2, locs) c =
>  pdT (r1,locs) c ++ pdT (r2,locs) c
> pdT (Star r, locs) c = 
>  [ (Seq r' (Star r), locs') | (r',locs') <- pdT (r,locs) c  ]


a PDMonad is a State Monad / Parsec

s is the probably the history of the locations that a match visited
a is the resulting pd

the monadic version is exactly the same as the pderivT modulo nubbing, which is not required for debugging purpose

> newtype PDMonad h a = PDMonad { runPDM :: h -> [(a,h)] } 
 
> instance Monad (PDMonad s) where
>    -- return :: a -> PDMonad s a
>    return a        = PDMonad (\h -> [(a,h)])
>    -- (>>=) :: PDMonad h a -> (a -> PDMonad h b) -> PDMonad h b
>    (PDMonad x) >>= f = PDMonad (\h -> concat [ runPDM (f a) h' | (a,h') <- x h ])


> instance MonadPlus (PDMonad [Loc]) where
>    mzero = PDMonad (\ls -> [])
>    p `mplus` q = PDMonad (\ls -> runPDM p ls ++ runPDM q ls)

                  
nubM does not really work, because the duplicate is introduced via the >>= operation.

> nubM :: Eq r => PDMonad h r -> PDMonad h r
> nubM pdm = PDMonad (\h -> nub2 (runPDM pdm h))

> start = flip runPDM

> addLoc :: Loc -> PDMonad [Loc] ()
> addLoc loc = PDMonad (\h -> [((),h++[loc])])

> pderivM :: RE -> Char -> PDMonad [Loc] RE
> pderivM Phi l = mzero
> pderivM Empty l = mzero
> pderivM (L l' loc) l | l' == l = addLoc loc >> return Empty
>                      | otherwise = mzero
> pderivM (Choice r1 r2) l = mplus (pderivM r1 l) (pderivM r2 l)
> pderivM (Star r) l = do { r' <- pderivM r l 
>                         ; return (Seq r' (Star r))
>                         }
> pderivM (Seq r1 r2) l
>     | isEmpty r1 = do                                   
>        { r1' <- pderivM r1 l
>        ; return (Seq r1' r2) } `mplus` pderivM r2 l
>     | otherwise = do 
>        { r1' <- pderivM r1 l
>        ; return (Seq r1' r2) }
                  


start [] (do { r1' <- pderivM r1 'A' ; r1'' <- nubM $ pderivM r1' 'A' ; pderivM r1'' 'A' })

> nub2 :: Eq a => [(a,b)] -> [(a,b)]
> nub2 = nubBy (\(p1,f1) (p2, f2) -> p1 == p2) 





> r = rAnnotate (Choice (Star (Seq (L 'A' 0) (L 'B' 0))) (L 'B' 0))   -- ((A,B)*|B)


> r1 = rAnnotate (Seq (Star (L 'A' 0)) (Star (L 'A' 0)))


> r2 = rAnnotate (Choice (Seq (L 'A' 0) (L 'A' 0)) (Seq (L 'A' 0) (L 'B' 0)))
