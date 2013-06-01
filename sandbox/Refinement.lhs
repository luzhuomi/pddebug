> {-# LANGUAGE GADTs #-}

The regular expression refinement algorithm

Inspired by the type checking system and type inference algorithm found in programming language research communities. \cite{TODO}

Type checking and Type inference algorithm 
==========================================

Type checking judgement
-----------------------

$\gamma \vdash e : t$ 
Given the type environemnt $\gamma$, the program expression e and the type $t$, the above is deducable if $e$ has type $t$ under the type environment $\gamma$

Note that the type checking is a relation, where $\gamma$, $e$ and $t$ are the inputs.

Type inference judgement 
------------------------

$\gamma \models e : t$

Given the type environment \gamma and the program expression e the algorithm reconstructs the type t.

Note that the type inference is considered an function, where \gamma and e are the inputs.

 * Type inference correctness

$\gamma \models e : t$ 
implies 
$\gamma \vdash e : t$ 




Regular expression debugging and reconstruction 
===============================================

The connection 
--------------

Pointed out the XDuce work, we consider the correspondence between the program expression $e$ and the document $d$,
the type $t$ and the regular expression $r$.

 * The word problem  $d \in r$ corresponds to the type checking problem.

The difference 
--------------

 * The matching problem 

 $$ d \in r \Longrightarrow \Delta $$ 

where r is annotated with label at each AST level. $\Delta$ maps labels to sub-matches.


The mechanism 
-------------

We use derivative (or partial derivative) operations to implement the word problem and the sub matching problem. See our recent papers (PPDP 12 )


The debugging algorithm 
-----------------------

Refer to the PDDebug.lhs

The Refinement checking judgement 
---------------------------------

> module Main where

> import qualified Data.Map as M
> import System.IO.Unsafe
> import Data.List 

> logger io = unsafePerformIO io

 * The problem 

Let  $\gamma$ denote the user specification, $d$ denote the input document , $r$ the pattern and  $r'$ the refined pattern, 
we use the judgement 
$$\gamma, r \vdash d : r'$$ 
to denote that under the user spec $\gamma$ , $r'$ is a replacement of $r$ that accepts $d$.

 * The user requirement 

\gamma ::= { (i, r) , ... , }
i ::= 1,2,3,...

> type UReq = [(Int, Re)]

> lookupUR :: Int -> UReq -> Maybe Re
> lookupUR i env = lookup i env

> updateUR :: Int -> Re -> UReq -> UReq
> updateUR x r ureq = map (\(y,t) -> if (x == y) then (y,r) else (y,t)) ureq

 * The Regular expression 
             
p ::= r^i 
r ::= () || (p|p) || pp || p* || l || \phi 
                          
> data Re where
>  Choice :: Int -> [Re] -> Re
>  Pair :: Int -> Re -> Re -> Re
>  Star :: Int -> Re -> Re
>  Ch :: Int -> Char -> Re
>  Eps :: Int -> Re
>  Phi :: Re
>  deriving (Show, Ord)


> instance Eq Re where
>     (==) (Choice _ rs1) (Choice _ rs2) = rs1 == rs2
>     (==) (Pair _ r1 r2) (Pair _ r1' r2') = r1 == r1' && r2 == r2'
>     (==) (Star _ r1) (Star _ r2) = r1 == r2
>     (==) (Ch _ c1) (Ch _ c2) = c1 == c2
>     (==) Eps{} Eps{} = True
>     (==) Phi Phi = True
>     (==) _ _ = False



> posEmpty :: Re -> Bool
> posEmpty (Eps _)        = True
> posEmpty (Choice _ rs)  = any posEmpty rs
> posEmpty (Pair _ r1 r2) = posEmpty r1 && posEmpty r2
> posEmpty (Star _ _)     = True
> posEmpty (Ch _ _)       = False
> posEmpty Phi            = False

> isPhi :: Re -> Bool 
> isPhi Phi            = True
> isPhi (Ch _ _ )      = False
> isPhi (Choice _ rs)  = all isPhi rs
> isPhi (Pair _ r1 r2) = isPhi r1 || isPhi r2 
> isPhi (Star _ _)     = False
> isPhi (Eps _)        = False

> isChoice :: Re -> Bool
> isChoice Choice{} = True
> isChoice _ = False

> deriv :: Re -> Char -> Re
> deriv r l = simpFix $ deriv' r l


> deriv' (Eps _) _ = Phi
> deriv' (Choice x rs) l = Choice x (map (\r -> deriv' r l) rs)
> deriv' (Pair x r1 r2) l | posEmpty r1 = Choice x [Pair x (deriv' r1 l) r2, deriv' r2 l]
>                        | otherwise = Pair x (deriv' r1 l) r2
> deriv' (Star x r) l = Pair x (deriv' r l) (Star x r)
> deriv' (Ch x c) l | c == l = (Eps x)
>                   | otherwise = Phi
> deriv' Phi _ = Phi


> simpFix :: Re -> Re
> simpFix p = let q = simp p
>             in if q == p
>                then q
>                else simpFix q


> simp :: Re  -> Re 
> simp (Pair l1 (Eps l2) r) 
>   | isPhi r   = Phi
>   | otherwise = r
> simp (Pair l r1 r2)
>   | isPhi r1 || isPhi r2 = Phi
>   | otherwise            = Pair l (simp r1) (simp r2)
> simp (Choice l []) = Eps l
> simp (Choice l [r]) = r
> simp (Choice l rs)
>  | any isChoice rs =  
>     Choice l $ 
>        foldl (\rs-> \r-> case r of
>                Choice l rs2 -> rs ++ rs2
>                _            -> rs ++ [r])
>              [] rs
>  | otherwise = Choice l $ nub $ filter (not.isPhi) $ map simp rs
> simp (Star l1 (Eps l2)) = Eps l2
> simp (Star l1 (Star l2 r)) = Star l1 r 
> simp (Star l r)
>  | isPhi r   = Eps l
>  | otherwise = Star l $ simp r 
> simp x = x 



> class Accept t where
>   accept :: t -> Doc -> Bool

> instance Accept Re where
>   accept r ls = posEmpty $ foldl (\r l -> deriv r l) r ls 

> type Doc = [Char]

> getLabel :: Re -> Maybe Int
> getLabel (Eps x)      = Just x
> getLabel (Choice x _) = Just x
> getLabel (Pair x _ _) = Just x
> getLabel (Star x _)   = Just x
> getLabel (Ch x _)     = Just x
> getLabel Phi          = Nothing

> dontcare = -1



> sigma :: Re -> String
> sigma (Choice _ rs) = nub $ concat $ map sigma rs
> sigma (Pair _ r1 r2) = nub $ (sigma r1) ++ (sigma r2)
> sigma (Star _ r) = sigma r
> sigma (Ch _ c) = [c]
> sigma Eps{} = []
> sigma Phi = []


 * The Replacement Relation 
We use the following judgement to denote the replacement relation
$$ \gamma, p \turns d : q $$ 
where $\gamma$ is the user requirement, $p$ is the existing regular expression, $d$ is the input document and $q$ is the replacement regular expression.
It reads, under user requirement $\gamma$, $p$ can be replaced by $q$ which accepts $d$. 

There are two properties follows 

 1. $d\in r \Longrightarrow \Delta$ implies $ \Delta \vdash \gamma$ and $r \subseq t$.
 2. $d \not \in r$ implies $r \gamma\over\approximate t$  and $d \in t \Longrightarrow \Delta$ and $\Delta \vdash \gamma$.

The first property ensures that the replacement is subsuming the orginal regex $r$ if $d$ is already in $r$ and the matching result is conforming to the user requirement.
The second property ensures that if $d$ is not in $r$, the replacement shall have the same requirement-shape as the orginal one and conform to the user requirement. 


> replacement :: UReq -> Re -> Doc -> Re -> Bool 

  i \in dom(\gamma) 
  d \in \gamma(i) 
  \gamma - {i}, r \vdash d, r'                           
 ----------------------------- (pExist)
  \gamma, r^i \vdash d : r'^i

> replacement = undefined       


   i \not \in dom(\gamma)
   \gamma - {i}, r \vdash d : r'
 ------------------------------- (pIgnore)
 \gamma, r^i \vdash d : r'^i


   d \in r
 ------------------------- (rEmp)
 \gamma, () \vdash d : r

   d \in r 
 ------------------------- (rLab)
 \gamma, l \vdash d : r



  fv(r1) = \bar{i1} fv(r2 = \bar{i2} 
 \gamma_{\bar{i1}}, r1 \vdash d1 : r1'                              
 \gamma_{\bar{i2}}, r2 \vdash d2 : r2'                         
 ------------------------------------- (rSeq)
 \gamma, r1r2 \vdash d1d2 : r1'r2'

 we use \gamma_{\bar{i}} to denote { (i,\gamma(i)) | i \in \bar{i} and i \in dom(\gamma) }
                          
                          
  \gamma, r1 \vdash d : r1'
 -------------------------------------- ( rOr1)   
 \gamma, r1|r2 \vdash d : r1'|r2                          


  \gamma, r2 \vdash d : r2'
 -------------------------------------- ( rOr2)   
 \gamma, r1|r2 \vdash d : r1|r2'                          


  \gamma, r \vdash di : r'  \forall i \in \{1,n\}
 ------------------------------------------------- ( rStar)   
 \gamma, r* \vdash d1...dn : r'*                          


Rules rSeq, rOr1, rOr2 and rStar validate the replacement relation indeterministically



  \gamma,p \vdash d:p'    \forall d\in D 
 ---------------------------------------- (pDocS)
  \gamma p \vdash D : p'






 *  The Refinement Algorithm 

We use the judgement 
$$\gamma,p \models d : q $$ 
to denote the refinement algorithm. 

The algorithm correctness property (Soundness)

Let $\gamma$ be the user requirement, $r$ denote the initial regular expression pattern, $d$ denote the input document
$\gamma, r \models d : r'$ implies $\gamma, r \vdash d : r'$.


> refine :: UReq -> Re -> Doc -> Maybe Re -- a Maybe monad is required in case of \gamma / l^x failure

 singleton(d) = r
 ----------------------------- (Phi1)
 \gamma, \phi \models d : r

  () \in r 
 -------------------------------------- (Emp1)
 \gamma, r^x \models () : r^x


  () \not \in r 
 -------------------------------------- (Emp2)
 \gamma r^x \models () : (r^x|()^x)^x

> refine ureq Phi [] = return (Eps dontcare)
> refine ureq Phi cs = return (singleton dontcare cs)

> refine ureq r [] | posEmpty r = return r
>                  | otherwise  = do { x <- getLabel r
>                                    ; return (Choice x [r, Eps x])
>                                    }

 p \norm (l1,p1,\bar{x1}


 -------------------------------------------
 \gamma, p \models ld : q


  r^x \norm (l1^x,p1)|...| (l^x,pi) |...|(ln^x,pn) -- todo which 'x'? it might not only be the top most 'x'!
  t/l^x = t'
  \{x : t'\} \cup \gamma, pi \models d : pi'
  (l1^x,p1)|...| (l^x,pi')|...|(ln^x,pn) \denorm r'^x
 ----------------------------------------------- (Norm1)
 \{x : t\} \cup \gamma, r^x \models ld : r'^x
                                            
                                            
  r^x \norm (l1^x,p1)|...|(ln^x,pn)
  \not \exists i \in \{1,n\} l_i = l
  ld \in t
  (l1^x,p1)|...|(ln^x,pn)|(l^x,d^x) \denorm r'^x                           
  ----------------------------------------------- (Norm2)
  \{x : t\} \cup \gamma, r^x \models ld : r'^x


 x \not \in dom(\gamma)
 r^x \norm (l1^x,p1)|...| (l^x,pi) |...|(ln^x,pn)
 \gamma, pi \models d : pi'                                    
  (l1^x,p1)|...| (l^x,pi')|...|(ln^x,pn) \denorm r'^x                              
 ----------------------------------------------- (Norm3)
 \gamma, r^x \models ld : r'^x
 

  x \not \in dom(\gamma)
  r^x \norm (l1^x,p1)|...|(ln^x,pn)
  \not \exists i \in \{1,n\} l_i = l  
  (l1^x,p1)|...|(ln^x,pn)|(l^x,d^x) \denorm r'^x                         
  ----------------------------------------------- (Norm4)
  \gamma, r^x \models ld : r'^x


> refine ureq r (l:d) = do 
>   { x <- getLabel r
>   ; case lookupUR x ureq of 
>     { Just t -> let t' = deriv t l
>                     ms = norm r
>                 in case lookupMN l ms of 
>                  { Just pi -> do 
>                     { let ureq' = updateUR x t' ureq
>                     ; pi' <- refine ureq' pi d
>                     ; let io = logger (putStrLn ("\n pi' = " ++ (show pi') ++ "l =" ++ (show l)))
>                     ; let ms' = io `seq` updateMN l pi' ms 
>                     ; let io = ms' `seq` logger (putStrLn ("\n ms' = " ++ (show ms')))
>                     ; io `seq` return (denorm ms')
>                     }
>                  ; Nothing 
>                     | t' `accept` d  -> do 
>                     { let ms' = insertMN l (singleton x d) ms
>                     ; return (denorm ms')
>                     }
>                     | otherwise -> Nothing
>                  }
>     ; Nothing -> let ms = norm r -- todo: check whether Norm3 and Norm4 are sound
>                  in case lookupMN l ms of 
>                  { Just pi -> do 
>                     { pi' <- refine ureq pi d
>                     ; let ms' = updateMN l pi' ms 
>                     ; return (denorm ms')
>                     }
>                  ; Nothing -> do 
>                     { let ms' = insertMN l (singleton x d) ms
>                     ; return (denorm ms')
>                     }
>                  }
>     }
>  }





  $p \norm m1 | ... | mn$ and $ m1 | ... | mn \denorm p$


> data Monomials = WithEps Int ( M.Map Char Re -- Maping l -> r
>                              , M.Map Re [Re] ) -- Mapping grouped by common trailing kleene's star expression
>                | WithoutEps Int ( M.Map Char Re -- Mapping l -> r
>                                 , M.Map Re [Re] ) -- Mapping r -> ls
>           deriving Show

norm r = if () \in r then (norm' r) | ()  else (norm' r)

                            
> norm :: Re -> Monomials                            
> norm Phi = error "applying norm to Phi"
> norm r | posEmpty r = WithEps x (norm' x r)
>        | otherwise  = WithoutEps x (norm' x r)
>    where Just x = getLabel r

norm' r = groupBy (eq . snd) [(l, r/l) | l \in \sigma(r)]

> norm' :: Int -> Re -> (M.Map Char Re, M.Map Re [Re])
> norm' x r = let ms = [ (l, deriv r l) | l <- sigma r ]
>             in (M.fromList ms, foldl (\m (r,l) -> upsert r [l] (++) m) M.empty (map (\(l,r) -> (tail_ r, Pair x (Ch x l) (init_ r))) ms))

tail_ returns the right most re in a sequence of Re

> tail_ :: Re -> Re 
> tail_ (Pair x r1 r2) = tail_ r2
> tail_ r = r

> init_ :: Re -> Re
> init_ (Pair x r1 r2) = let r2' = (init_ r2)
>                        in case r2' of { Eps _ -> r1; _ -> Pair x r1 r2' }
> init_ r = Eps dontcare

append_ appends two Re(s) by sequence

> append_ :: Int -> Re -> Re -> Re
> append_ _ (Pair y r1 r2) r3 = Pair y r1 (append_ y r2 r3)
> append_ x r1 r2 = Pair x r1 r2

> upsert :: Ord k => k -> v -> (v -> v -> v) -> M.Map k v -> M.Map k v
> upsert k v f m = case M.lookup k m of 
>                  { Just v' -> M.adjust (\_ -> f v' v) k m 
>                  ; Nothing -> M.insert k v m }

> lookupMN :: Char -> Monomials -> Maybe Re
> lookupMN c (WithEps x (m1,m2)) = M.lookup c m1
> lookupMN c (WithoutEps x (m1,m2)) = M.lookup c m1

> updateMN :: Char -> Re -> Monomials -> Monomials
> updateMN c r (WithEps x (m1,m2)) = 
>    let r' = tail_ r   -- the tail
>        r'' = Pair x (Ch x c) (init_ r) -- the label + the prefix
>    in WithEps x (M.adjust (\_ -> r) c m1, upsert r' [r''] (++) m2)  -- the subfix r' might not be in m2
> updateMN c r (WithoutEps x (m1,m2)) = 
>    let r' = tail_ r   
>        r'' = Pair x (Ch x c) (init_ r)
>    in WithoutEps x (M.adjust (\_ -> r) c m1, upsert r' [r''] (++) m2) 

> insertMN :: Char -> Re -> Monomials -> Monomials
> insertMN c r (WithEps x (m1,m2)) = 
>    let r' = tail_ r   
>        r'' = Pair x (Ch x c) (init_ r)  
>    in WithEps x (M.insert c r m1, upsert r' [r''] (++) m2) 
> insertMN c r (WithoutEps x (m1,m2)) = 
>    let r' = tail_ r   
>        r'' = Pair x (Ch x c) (init_ r)
>    in WithoutEps x (M.insert c r m1, upsert r' [r''] (++) m2) 

> singleton :: Int -> Doc -> Re 
> singleton x cs = foldr (\l r -> Pair x (Ch x l) r) (Eps x) cs


return a choice if the list is non-singleton

> mkChoice :: Int -> [Re] -> Re 
> mkChoice x [r] = r
> mkChoice x rs = Choice x rs

denorm (\bar{m}|()) = let (pluses, nonpluses) = splitBy isPlusMonomial $ denorm' \bar{m}                           
                      in [ (mkStar plus) | plus <- pluses ] ++ nonpluses
                          
denorm \bar{m} = let (pluses, nonpluses) = splitBy isPlusMonomial $ denorm' \bar{m}
                 in [ (mkPlus plus) | plus <- pluses ]  ++ nonpluses


> denorm :: Monomials -> Re
> denorm (WithEps x (m1,m2)) = 
>    let (plusMonoGrp, nonPlusMonoGrp) = part m2 
>        ps = map mkStar (M.toList plusMonoGrp)         
>        nps = map (\(tl, its) -> append_ x (mkChoice x its) tl) (M.toList nonPlusMonoGrp)
>    in simpFix $ mkChoice x (ps ++ nps)
> denorm (WithoutEps x (m1,m2)) = 
>    let (plusMonoGrp, nonPlusMonoGrp) = part m2 
>        ps = map mkPlus (M.toList plusMonoGrp)         
>        nps = map (\(tl, its) -> append_ x (mkChoice x its) tl) (M.toList nonPlusMonoGrp)
>    in simpFix $ mkChoice x (ps ++ nps)


> mkStar :: (Re, [Re]) -> Re
> mkStar = fst

> mkPlus :: (Re, [Re]) -> Re
> mkPlus (Star x r,its) = Pair x r (Star x r)


partition map by plus monomial and non plus monomial

> part :: M.Map Re [Re] -> (M.Map Re [Re] , M.Map Re [Re])
> part m = M.partitionWithKey (\ r rs -> isPlusMN rs r ) m


a monomial is a plus mono iff m = (p1|...|pn, r*) and (p1|...|pn) \equiv r and r 

isPlus (p1|...|pn) r* = (p1|...|pn) <= r and r <= (p1|...|pn)

> isPlusMN :: [Re] -> Re -> Bool
> isPlusMN ps (Star x r) = ((Choice dontcare ps) `subsumedBy` r) && (r `subsumedBy` (Choice dontcare ps))
> isPlusMN ps _ = False

the containment check

> subsumedBy :: Re -> Re -> Bool
> subsumedBy r1 r2 = subsumedBy' M.empty r1 r2

> data Leq = Leq Re Re deriving (Eq, Ord, Show)

> subsumedBy' :: M.Map Leq () -> Re -> Re -> Bool
> subsumedBy' env Phi _ = True
> subsumedBy' env r1 r2 = 
>   case M.lookup (Leq r1 r2) env of   
>    { Just _  -> True  
>    ; Nothing | posEmpty r1 && not (posEmpty r2) -> False
>              | otherwise -> let env' = M.insert (Leq r1 r2)  () env
>                             in  all (\l -> subsumedBy' env' (deriv r1 l) (deriv r2 l)) (sigma (Choice dontcare [r1,r2]))
>    }

                          
                          
denorm' \bar{m} = groupBy (eq . snd) [(l, r/l) | l \in \sigma(r)]

isPlusMonomial (l,p) = l \in (choiceToList p)

mkStar ms = let fs = map fst ms  
                (Star r) = snd (head ms)
            in if (sort fs) == (sort (choiceToList r)) then (Star r) else ms

mkPlus ms = let fs = map fst ms  
                (Star r) = snd (head ms)
            in if (sort fs) == (sort (choiceToList r)) then (r, (Star r)) else ms
                          
r1 = (A|B)*

> r1 = Star 1 (Choice 2 [Ch 3 'A', Ch 4 'B'])

r2 = (A|B|C)*

> r2 = Star 1 (Choice 2 [Ch 3 'A'])

r3 = .+

> r3 = Pair dontcare (Choice dontcare [Ch dontcare 'A',Ch dontcare 'B',Ch dontcare 'C']) (Star dontcare (Choice dontcare [Ch dontcare 'A',Ch dontcare 'B',Ch dontcare 'C']))



> v = "ABC"

> g = [(1::Int, r3)]
