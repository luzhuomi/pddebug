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
> import qualified Data.IntMap as IM
> import System.IO.Unsafe
> import Data.List 
> import Data.Maybe

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

> allAccEps :: UReq -> Bool
> allAccEps ureq = all (\(x,t) -> posEmpty t) ureq

> inUR :: Int -> UReq -> Bool
> inUR i env = isJust (lookupUR i env) 

 * The Regular expression 
             
p ::= r^i 
r ::= () || (p|p) || pp || p* || l || \phi 
                          
> data Re where
>  Choice :: [Int] -> [Re] -> Re
>  Pair :: [Int] -> Re -> Re -> Re
>  Star :: [Int] -> Re -> Re
>  Ch :: [Int] -> Char -> Re
>  Eps :: [Int] -> Re
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



> class PDeriv t where
>   pderiv :: t -> Char -> [Re]


partial derivatives of regex

> instance PDeriv Re where
>   pderiv (Eps _) _ = []
>   pderiv (Choice x rs) l = nub $ concatMap (\r -> pderiv r l) rs -- x?
>   pderiv (Pair x r1 r2) l | posEmpty r1 = nub [ Pair x r1' r2 | r1' <- pderiv r1 l] ++ (pderiv r2 l)
>                           | otherwise =  [ Pair x r1' r2 | r1' <- pderiv r1 l]
>   pderiv (Star x r) l = [ Pair x r' (Star x r) | r' <- pderiv r l ]
>   pderiv (Ch x c) l | c == l = [ Eps x ]
>                     | otherwise = []
>   pderiv Phi _ = []

 * partial derivatives of a set of regexs

> instance PDeriv t => PDeriv [t] where
>   pderiv rs l = concatMap (\r -> pderiv r l) rs

* partial dervatives extended to user-requirement-regex pair

We need to annotate the URPair with the recommendation info to 'disambiguate' the refinement process. 
To elaborate, we first need to consider the extension of partial derivative operation over the user-requirement-regex pairs.

 ** Case: i \not\in dom(\gamma)
                    
  (\gamma, \epsilon_i) / l = {}                 -- (Eps1) 
  (\gamma, l_i) / l = { (\gamma, \epsilon_i) }  -- (LabMatch1)
  (\gamma, l_i') / l = { }                      -- (LabMisMatch1)                   
  (\gamma, (r1r2)_i) /l | \epsilon \in r1 = { (\gamma' ++ \gamma(fv(r2)), (r1'r2)_i) | (\gamma', r1') <- (\gamma(fv(r1)), r1) / l } ++  (\gamma(fv(r2)), r2) / l
                        | otherwise  = { (\gamma' ++ \gamma(fv(r2)), (r1'r2)_i) | (\gamma', r1') <- (\gamma(fv(r1)), r1) / l }   
                                                -- (Pair1) 
  (\gamma, (r1|r2)_i) / l = (\gamma(fv(r1_i)), r1_i)/l ++ (\gamma(fv(r2_i)), r2_i)/l   -- (Choice1)
  (\gamma, r*_i) / l = { (\gamma', (r'r*)_i) | (\gamma', r') <- (\gamma, r) / l }      -- (Star1)
                    
 ** Case: i \in dom(\gamma)
  (\gamma, \epsilon_i) / l = {}                 -- (Eps2) 
  (\gamma, l_i) / l = { (\gamma,\epsilon_i) }   -- (LabMatch2)
  (\gamma, l_i') / l = { }                      -- (LabMisMatch2)                   
  (\gamma, (r1r2)_i) /l | \epsilon \in r1 = { (\gamma' ++ \gamma(fv(r2)) ++ { (i, \gamma(i)/l) } , (r1'r2)_i) | (\gamma', r1') <- (\gamma(fv(r1)), r1) / l } ++  (\gamma(fv(r2)), r2) / l
                        | otherwise  = { (\gamma' ++ \gamma(fv(r2)), (r1'r2)_i) | (\gamma', r1') <- (\gamma(fv(r1)), r1) / l }
                                                -- (Pair2)
  (\gamma, (r1|r2)_i) /l = (\gamma(fv(r1_i)), r1_i)/l ++ (\gamma(fv(r2_i)), r2_i) /l  -- (Choice2)
  (\gamma, r*_i) / l = { (\gamma', (r'r*)_i) | (\gamma', r') <- (\gamma, r) / l }     -- (Star2)
                    
                    
                  
NOTE: \gamma([i1,...,in]) denotes { (i,r) | (i,r) \in \gamma, i \in { i1,..., in } }                  
               
  The above formulation does not refine in case of failure, i.e. pd yields { }. See cases (Eps1), (Eps2), (LabMistMach1) and (LabMistMach2).
                  

e.g. given p = x :: (a|b)*  and w = c, matching w with p using partial derivative operation
 
                  p / c = {} 
                  
                  whichis a matching failure
                  
 This is because p / c -->                   
                 { (r, p) | r <- (a|b) /c }
     and                  
                 (a|c) / c -->
                 a/c U b/c -->
                  {} U {}  --> 
                     {}
                  
Suppose the user requirement enforces that x should match with a non-empty word e.g. { x :: .+ }, note that '.' matches with any single symbol.

One naive way to refine the pattern p is to just update by replacing (a|b)* with .+, however doing so is often too liberal, because the user requirement could be specified loosely.

An immediate (less naive) fix would be adjusting the partial derivative operations as follows,


 We adjust the pd operation to return the refinement environment besides the partial derivatives

 ** Case: i \not\in dom(\gamma)
                    
  (\gamma, \epsilon_i) / l = { (\gamma, \epsilon_j, {i : seq+ l_j weak}) }                   -- (Eps1') 
  (\gamma, l_i) / l        = { (\gamma, \epsilon_i, {}) }                                    -- (LabMatch1)
  (\gamma, l'_i) / l       = { (\gamma, \epsilon_i, {i : choice+ l_j weak}) }                -- (LabMisMatch1')                   
  (\gamma, (r1r2)_i) /l | \epsilon \in r1 = { (\gamma' ++ \gamma(fv(r2)), (r1'r2)_i, \theta) | (\gamma', r1', \theta) <- (\gamma(fv(r1)), r1) / l } ++  (\gamma(fv(r2)), r2) / l
                        | otherwise       = { (\gamma' ++ \gamma(fv(r2)), (r1'r2)_i, \theta) | (\gamma', r1'. \theta) <- (\gamma(fv(r1)), r1) / l }  
                                                                                             -- (Pair1)                                               
  (\gamma, (r1|r2)_i) / l = (\gamma(fv(r1_i)), r1_i)/l ++ (\gamma(fv(r2_i)), r2_i)           -- (Choice1)
  (\gamma, r*_i) / l = { (\gamma', (r'r*)_i) | (\gamma', r', \theta) <- (\gamma, r) / l }    -- (Star1)
                    
 ** Case: i \in dom(\gamma)
  (\gamma, \epsilon_i) / l = { (\gamma', \epsilon_j, {i : seq+ l_j strong}) | \gamma' <- \gamma / l }   -- (Eps2') 
  (\gamma, l_i) / l        = { (\gamma,  \epsilon_i, {}) }                                              -- (LabMatch2)             
  (\gamma, l_i') / l       = { (\gamma', \epsilon_i, {i : choice+ l_j strong}) | \gamma' <- \gamma / l} -- (LabMisMatch2')                   
  (\gamma, (r1r2)_i) /l | \epsilon \in r1 = { (\gamma' ++ \gamma(fv(r2)) ++ { (i, \gamma(i)/l) } , (r1'r2)_i, \theta) | (\gamma', r1', \theta) <- (\gamma(fv(r1)), r1) / l } ++  (\gamma(fv(r2)), r2) / l
                        | otherwise       = { (\gamma' ++ \gamma(fv(r2)) ++ { (i, \gamma(i)/l)}, (r1'r2)_i, \theta) | (\gamma', r1', \theta) <- (\gamma(fv(r1)), r1) / l }
                                                                                                        -- (Pair2)
  (\gamma, (r1|r2)_i) /l   = (\gamma(fv(r1_i)), r1_i)/l ++ (\gamma(fv(r2_i)), r2_i) /l                  -- (Choice2)
  (\gamma, r*_i) / l       = { (\gamma', (r'r*)_i, \theta) | (\gamma', r', \theta) <- (\gamma, r) / l } -- (Star2)
                    

We aggressively provide suggestions \theta to those partial derivative cases which yields empty set, ref to case (Eps1'), (LabMisMatch1'), (Eps2') and (LabMisMatch2').

The refinement suggestion \theta is defined as follows,

 \theta ::= { 1:rop1, ..., n : rop_n }
                   where 1..n are labels 
 rop ::= (seq+ l_i level) | (choice+ l_i level)                     
 level ::= weak | strong                  


The problem with the above adjustment is that we will end up with many unwanted refinement and the size of the regex is blown up. 
Let's consider an example. 

Example 1:
(\gamma, (a_1|b_2)_0*_3) / b = { (\gamma',(r',(a_1|b_2)_0*_3)_3) | (\gamma',r') <- (\gamma, (a_1|b_2)_0) / b }  
because
(\gamma, (a_1|b_2)_0) / b = { (\gamma, \epsilon_1_0), (\gamma, \epsilon_2_0) } -- note that thanks to  (LabMisMatch1'), the first epsilon was produced by \gamma,a / b

As a result 

(\gamma, (a_1|b_2)_0*_3) / b = { (\gamma',(\epsilon_1_0,(a_1|b_2)_0*_3)_3) , (\gamma',(\epsilon_2_0,(a_1|b_2)_0*_3)_3) }   -- (10)

apply denormalization, (denorm goes by the annotation _i)

there are two monomials
the monomial is not affected by the refinement 
(a, { (\epsilon_1_0, (a_1|b_2)_0*_3) } )
the other monomial is affected by the refinement, derived from  (10) by removing the \gamma'
(b, { (\epsilon_1_0,(a_1|b_2)_0*_3) , (\epsilon_2_0,(a_1|b_2)_0*_3)_3 }) 


applying de-normalization to the above two monomials,

(a, { (\epsilon_1_0, (a_1|b_2)_0*_3) } ) ~> (a_1| __ ) (a_1|b_2)_0*_3   -- we push a back to a_1, by treating "\epsilon_1_0" is the place holder for 'a'

(b, { (\epsilon_1_0,(a_1|b_2)_0*_3) , (\epsilon_2_0,(a_1|b_2)_0*_3)_3 })  ~>  ( b_1 | b_2 ) (a_1|b_2)_0*_3 


Note that the b_1 is created by an unnecessary refinement step. If we combine, we have (a_1 | b_1 | b_2) (a_1|b_2)_0*_3 , 


the denorm will "generalize" it into a star exp ((a|b)_1 | b_2)_0*_3 which is extended unnecessary. (we will show how the
generalization work later) \kl{maybe we should start showing how the normalization and denormalization work?

The problem is how shall we get rid of b_1?


Let's consider another example


Example 2:

({ (1 : (a|c)) }, (a_1|b_2)_0*_3) / c  = 
  { (\gamma',(r',(a|b)*)) | (\gamma',r') <- ({ (1 : (a|b|c)) }, (a_1|b_2)_0) / c }      
  =                    

({ (1 : (a|c)) }, (a_1|b_2)_0 ) / c = { ( { 1:\epsilon } , \epsilon_1_0), ( { } , \epsilon_2_0) }

hence the monomials
(a, {(\epsilon_1_0, (a_1|b_2)_0*_3)} )    ~> (a_1_0, (a_1|b_2)_0*_3)
(b, {(\epsilon_2_0, (a_1|b_2)_0*_3)} )    ~> (b_2_0, (a_1|b_2)_0*_3)   
(c, {(\epsilon_1_0, (a_1|b_2)_0*_3), (\epsilon_2_0, (a_1|b_2)_0*_3)} )  ~> (c_1_0|c_2_0), (a_1|b_2)_0*_3)   

Note that either c_1_0 or c_2_0 is an redundant result of refinement. So now the question is which one to removed?

In this case, it seems that c_1_0 should be the one to be kept, since the user requirement { (1 : (a|c)) } suggest that 
the c can be added under 1.


The trick is to annotate the pd with the "recommendation" info.


Let recommendation defined as

 rec :: = s | w | f

where f > s > w

PD of (\gamma,r) /l added with recommendation info

 ** Case: i \not\in dom(\gamma)
                    
  (\gamma, \epsilon_i) / l = { (\gamma, \epsilon_i, w) }   (Eps1') 
  (\gamma, l_i) / l = { (\gamma, \epsilon_i, f) } (LabMatch1)
  (\gamma, l_i') / l = { (\gamma, \epsilon_i, w) } (LabMisMatch1')                   
                  
  (\gamma, (r1r2)_i) /l | \epsilon \in r1 = { (\gamma' ++ \gamma(fv(r2)), (r1'r2)_i, rec) | (\gamma', r1', rec) <- (\gamma(fv(r1)), r1) / l } ++  (\gamma(fv(r2)), r2) / l
                        | otherwise  = { (\gamma' ++ \gamma(fv(r2)), (r1'r2)_i, rec) | (\gamma', r1', rec) <- (\gamma(fv(r1)), r1) / l }
  (\gamma, (r1|r2)_i) / l = (\gamma(fv(r1_i)), r1_i)/l ++ (\gamma(fv(r2_i)), r2_i) 
  (\gamma, r*_i) / l = { (\gamma', (r'r*)_i, rec) | (\gamma', r', rec) <- (\gamma, r) / l }
                    
 ** Case: i \in dom(\gamma)
  (\gamma, \epsilon_i) / l = { ( \gamma-i U (i,r'), r'_i, s) | r' \in \gamma(i) / l }   (Eps2')   
  (\gamma, l_i) / l = { ( \gamma-i U (i,r'), \epsilon_i, f) } (LabMatch2)
  (\gamma, l_i') / l = { ( \gamma-i U (i,r'), r'_i, s) | r' \in \gamma(i) / l }   (LabMisMatch2')
                  
  (\gamma, (r1r2)_i) /l | \epsilon \in r1 = { (\gamma' ++ \gamma(fv(r2)) ++ { (i, |\gamma(i)/l } , (r1'r2)_i, rec) | (\gamma', r1', rec) <- (\gamma(fv(r1)), r1) / l } ++  (\gamma(fv(r2)), r2) / l
                        | otherwise  = { (\gamma' ++ \gamma(fv(r2)), (r1'r2)_i, rec) | (\gamma', r1', rec) <- (\gamma(fv(r1)), r1) / l }
  (\gamma, (r1|r2)_i) /l = (\gamma(fv(r1_i)), r1_i)/l ++ (\gamma(fv(r2_i)), r2_i) /l 
  (\gamma, r*_i) / l = { (\gamma', (r'r*)_i, rec) | (\gamma', r', rec) <- (\gamma, r) / l }


with the recommendation info, we now re-run the above two examples.

Example 1 (revisited):
(\gamma, (a_1|b_2)_0*_3) / b = { (\gamma',(r',(a_1|b_2)_0*_3)_3) | (\gamma',r',rec) <- (\gamma, (a_1|b_2)_0) / b }  
because
(\gamma, (a_1|b_2)_0) / b = { (\gamma, \epsilon_1_0, w), (\gamma, \epsilon_2_0, f) } 
Since these two states are overlapping, hence the weak recommendation is removed in the presence of f

The duplication is removed based on the ordering of the recommendation info
Given { (\gamma1, r, rec_1) , (\gamma1, r, rec_2) },
 (\gamma1, r, rec_2) is removed iff rec_2 <= rec_1


As a result 

(\gamma, (a_1|b_2)_0*_3) / b = { (\gamma',(\epsilon_2_0,(a_1|b_2)_0*_3)_3) }   -- (10)

The denormalization yields (a_1|b_2)_0*_3 (no refinement is required)



Example 2 (revisited): 

({ (1 : (a|c)) }, (a_1|b_2)_0*_3) / c  = 
  { (\gamma',(r',(a|b)*),rec ) | (\gamma',r',rec) <- ({ (1 : (a|b|c)) }, (a_1|b_2)_0) / c }      
  =                    

({ (1 : (a|c)) }, (a_1|b_2)_0 ) / c = { ( { 1:\epsilon } , \epsilon_1_0, s), ( { } , \epsilon_2_0, w) }

Again the two resulting states are overlappng, we remove the weak recommendation in the presence of the strong recommendation

Thus, we have the following monomials
(a, {(\epsilon_1_0, (a_1|b_2)_0*_3)} )    ~> (a_1_0, (a_1|b_2)_0*_3)
(b, {(\epsilon_2_0, (a_1|b_2)_0*_3)} )    ~> (b_2_0, (a_1|b_2)_0*_3)   
(c, {(\epsilon_1_0, (a_1|b_2)_0*_3)} )  ~> (c_1_0, (a_1|b_2)_0*_3)   

the final denormalization yields 

((a_1|c_1)|b_2)_0 ((a_1|b_2)_0*_3) 

hence will be generalized to
(((a_-1|c_-1)_1|b_2)_0*_3) 


> {- 

> data URPair = URPair UReq Re Recommend deriving (Show, Eq)

> data Recommend = Strong | Weak | Fixed deriving (Show, Eq)

> instance Ord Recommend where
>   compare Fixed Fixed = EQ
>   compare Fixed _     = GT
>   compare Strong Strong = EQ
>   compare Strong Weak = GT
>   compare Strong Fixed = LT
>   compare Weak Weak = EQ
>   compare Weak _ = LT

> class URPDeriv t where
>   urPDeriv :: t -> Char -> [URPair]

> instance URPDeriv URPair where
>   urPDeriv (URPair ureq (Eps (i:is)) rec) l
>     | i `inUR` ureq = [ URPair (updateUR i r' ureq) (annotate (i:is) r') Strong
>                        | r' <- pderiv (fromJust (lookupUR i ureq)) l  ]
>     | otherwise   = [ URPair ureq (Eps (i:is)) Weak ]
>   urPDeriv (URPair ureq (Ch (i:is) l) rec) l' 
>     | i `inUR` ureq && l == l' = [ URPair (updateUR i r' ureq) (Eps (i:is)) Fixed
>                                   | r' <- pderiv (fromJust (lookupUR i ureq)) l  ]
>     | i `inUR` ureq && l /= l' = [ URPair (updateUR i r' ureq) (annotate (i:is) r') Strong
>                                    | r' <- pderiv (fromJust (lookupUR i ureq)) l  ]
>     | not (i `inUR` ureq) && l == l' = [ URPair ureq (Eps (i:is)) Fixed ]
>     | otherwise = [ URPair ureq (Eps (i:is)) Weak ]
>   urPDeriv = undefined -- TODO


> instance URPDeriv t => URPDeriv [t] where
>   urPDeriv urs l = concatMap (\ur -> urPDeriv ur l) urs -- nub?

> -}


partial derivative
  
  

> class Accept t where
>   accept :: t -> Doc -> Bool

> instance Accept Re where
>   accept r ls = any posEmpty $ foldl (\rs l -> pderiv r l) [r] ls 

> instance Accept t => Accept [t] where
>   accept rs ls = any (\r -> accept r ls) rs

> type Doc = [Char]

> getLabels :: Re -> [Int]
> getLabels (Eps x)      = x
> getLabels (Choice x rs) = x ++ concatMap getLabels rs
> getLabels (Pair x r1 r2) = x ++ (getLabels r1) ++ (getLabels r2)
> getLabels (Star x r)   = x ++ (getLabels r)
> getLabels (Ch x _)     = x
> getLabels Phi          = []



> getLabel :: Re -> [Int]
> getLabel (Eps x)      = x
> getLabel (Choice x _) = x
> getLabel (Pair x _ _) = x
> getLabel (Star x _)   = x
> getLabel (Ch x _)     = x
> getLabel Phi          = []

> dontcare = []


> annotate :: [Int] -> Re -> Re
> annotate is (Eps _) = Eps is
> annotate is (Choice x cs) = Choice is cs
> annotate is (Pair x r1 r2) = Pair is r1 r2
> annotate is (Star x r) = Star is r
> annotate is (Ch x c) = Ch is c
> annotate is Phi = Phi


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


  \gamma, r \vdash di : r'  \forall i \in {1,n}
 ------------------------------------------------- ( rStar)   
 \gamma, r* \vdash d1...dn : r'*                          


Rules rSeq, rOr1, rOr2 and rStar validate the replacement relation indeterministically



  \gamma,p \vdash d:p'    \forall d\in D 
 ---------------------------------------- (pDocS)
  \gamma p \vdash D : p'






 * The Refinement Algorithm 

Naively, we use the judgement 
$$\gamma,p \models d : q $$ 
to denote the refinement algorithm. 


However this is NOT going to work, consider the following example

\gamma = { (1 : .+ ) (2 : .+) }
r = ((A*)(A*))
 or in explicit annotation
r = (0 :: ( (1 :: A*) (2 :: A*)))

d = A

Note that r is ambigous. If we send A to (1 :: A*), we have the result
\gamma = { (1 : .* ) (2 : .+) } and r = ((A*),(A*)) as we not only 
consume the A in (1:: A*), but also update \gamma.

If we send A to (2 :: A*), the resulting pair will be different
\gamma = { (1 : .+ ) (2 : .*) } and r = ((A*),(A*))

In summary, when we perform partial derivative operation, the \gamma and the r go
together in pairs.

Hence we use the judgement
$${ (\gamma_1,p_1), ..., (\gamma_n,p_n) } \models d : {q_1,...,q_m} $$ 

where 
${ (\gamma_1,p_1), ..., (\gamma_n,p_n) }$ are the user requirement and orginal 
sub regex (nfa state) pairs. ${q_1,...,q_m}$ denotes the output set of 
refined sub regex (nfa state).





The algorithm correctness property (Soundness)

Let $\gamma$ be the user requirement, $r$ denote the initial regular expression pattern, $d$ denote the input document
$ { \gamma, r } \models d : { r1', ... , rn' } $ implies $\gamma, r \vdash d : r1'|...|rn'$.


                          
r1 = (A|B)*

> r1 = Star [1] (Choice [2] [Ch [3] 'A', Ch [4] 'B'])

r2 = (A|B|C)*

> r2 = Star [1] (Choice [2] [Ch [3] 'A'])


> r3 = Pair [1] (Ch [2] 'A') (Ch [3] 'B')

r4 = ()

> r4 = Eps [1] 

t3 = .+

> t3 = Pair dontcare (Choice dontcare [Ch dontcare 'A',Ch dontcare 'B',Ch dontcare 'C']) (Star dontcare (Choice dontcare [Ch dontcare 'A',Ch dontcare 'B',Ch dontcare 'C']))

> t4 = Pair dontcare (Choice dontcare [Ch dontcare 'A',Ch dontcare 'B']) (Star dontcare (Choice dontcare [Ch dontcare 'A',Ch dontcare 'B']))


> v = "ABC"

> g1 = [(1::Int, t3)]

> g2 = [(1::Int, t4)]



New idea: refinement algo takes ureq re pair and the input words returns a set of 

```
----------------------------------------------------------------------------------------------------------------------------------- (Eps)
\overline{ \gamma, r, \Psi } |=  \epsilon: { \Psi | (\gamma, r, \Psi) \in \overline{ \gamma, r, \Psi }, \epsilon \in \Psi(r)  } ++ 
                                           { \Psi . (i -> +\epsilon, s) } | (\gamma, r, \Psi) \in  \overline{ \gamma, r, \Psi } }
      
      
      
\overline{ \gamma, r, \Psi } / l = \overline { \gamma', r', \Psi' } 
\overline { \gamma', r', \Psi o \Psi'  } |= w: \overline {\Psi''} 
----------------------------------------------------------------------------------------------------------------------------------- (Ind)
\overline{ \gamma, r, \Psi } |=  lw : {\Psi''}
      
```

Note that from (Ind) the refinement environment \Psi is passed along


> type REnv = IM.IntMap [ROp]

> data ROp = RAdd Re RLevel 
>          | RApp Re RLevel
>           deriving (Eq,Show)


> compareREnv :: REnv -> REnv -> Ordering
> compareREnv r1 r2 = 
>   let s1 = renvSize r1  
>       s2 = renvSize r2 
>   in case compare s1 s2 of 
>       EQ -> let w1 = renvWeak r1
>                 w2 = renvWeak r2
>             in case compare w1 w2 of
>                EQ -> let a1 = renvRApp r1
>                          a2 = renvRApp r2
>                      in compare a1 a2
>                _ -> compare w1 w2
>       _  -> compare s1 s2

count the number of ROps in renv

> renvSize :: REnv -> Int
> renvSize renv = sum (map (\ (k,v) -> length v) (IM.toList renv))

> renvStrong :: REnv -> Int
> renvStrong renv = sum (map (\ (k,v) -> length (filter isStrong v)) (IM.toList renv))

> renvWeak :: REnv -> Int
> renvWeak renv = sum (map (\ (k,v) -> length (filter isWeak v)) (IM.toList renv))

> renvRApp :: REnv -> Int
> renvRApp renv = sum (map (\ (k,v) -> length (filter isRApp v)) (IM.toList renv))

                         
                         
> isStrong :: ROp -> Bool
> isStrong (RAdd _ Strong) = True                         
> isStrong (RAdd _ _) = False
> isStrong (RApp _ Strong) = True                         
> isStrong (RApp _ _) = False


> isWeak :: ROp -> Bool
> isWeak (RAdd _ Weak) = True                         
> isWeak (RAdd _ _) = False
> isWeak (RApp _ Weak) = True                         
> isWeak (RApp _ _) = False

> isRAdd :: ROp -> Bool
> isRAdd (RAdd _ _) = True
> isRAdd _ = False

> isRApp :: ROp -> Bool
> isRApp (RApp _ _) = True
> isRApp _ = False

                       
                       
> data RLevel = Strong | Weak deriving (Ord, Eq, Show)

> refine :: UReq -> Re -> [Char] -> [Re]
> refine ureq r cs = 
>   let renvs = nub $ sortBy compareREnv (ref [(ureq, r, IM.empty)] cs)
>   in  map (\renv -> apply renv r)  renvs

> ref :: [(UReq, Re, REnv)] -> [Char] -> [REnv]
> ref urs [] = [ renv | (ureq, r, renv) <- urs, posEmpty (renv `apply` r) ] ++ 
>              [ extend renv (getLabel r) (RAdd (Eps dontcare) Strong)
>                     | (ureq, r, renv) <- urs
>                     , not (posEmpty (renv `apply` r))
>                     , any (\i -> case lookupUR i ureq of
>                                  { Nothing -> False
>                                  ; Just t  -> posEmpty t }) (getLabel r) ]
> ref urs (l:w) = let urs' = concatMap (\ (ur,r,renv) -> 
>                                     let urs'' = urePDeriv (ur, r, renv) l
>                                     in  map (\(ur', r', renv') -> (ur', r',  combine renv renv')) urs'') urs
>                 in ref urs' w




> urePDeriv :: (UReq, Re, REnv) -> Char -> [(UReq, Re, REnv)]
> urePDeriv (ur, r, psi) l = let max_i = maximum $ getLabels (psi `apply` r)
>                            in urPDeriv (ur,psi `apply` r) l (max_i + 1)



> urPDeriv :: (UReq, Re) -> Char -> Int -> [(UReq, Re, REnv)]
> urPDeriv (ur, Eps (i:is)) l next_i
>   | i `inUR` ur = [ ((updateUR i r' ur), Eps [next_i], IM.singleton i [RApp (Ch [next_i] l) Strong]) 
>                      | let r = fromJust (lookupUR i ur), r' <- pderiv r l ]
>   | otherwise   = [ (ur, Eps [next_i], IM.singleton i [RApp (Ch [next_i] l) Weak]) ]
> urPDeriv (ur, (Ch (i:is) l)) l' next_i = 
>   case lookup i ur of 
>     { Just r | l == l' -> [ ((updateUR i r' ur), (Eps (i:is)), IM.empty )
>                            | r' <- pderiv r l ]
>              | l /= l' -> [ ((updateUR i r' ur), (Eps (i:is)), IM.singleton i [RAdd (Ch [next_i] l') Strong]) | r' <- pderiv r l]
>     ; Nothing | l == l' -> [ (ur, Eps (i:is), IM.empty ) ]
>               | l /= l' -> [ (ur, Eps (i:is), IM.singleton i [RAdd (Ch [next_i] l') Weak] ) ] 
>     }
> urPDeriv (ur, Pair (i:is) r1 r2) l next_i =
>    case lookup i ur of 
>     { Just p -> 
>         case pderiv p l of
>           { [] -> [] 
>           ; ps  | posEmpty r1 -> [ ((ur' ++ ur `limit` (fv r2) ++ [(i, Choice dontcare ps)]) , (Pair (i:is) r1' r2), renv) |  (ur', r1', renv) <- urPDerivS (ur `limit` (fv r1), r1) l next_i ] ++ (urPDerivS (ur `limit` (fv r2), r2) l next_i)
>                 | otherwise   -> [ ((ur' ++ ur `limit` (fv r2) ++ [(i, Choice dontcare ps)]) , (Pair (i:is) r1' r2), renv) |  (ur', r1', renv) <- urPDerivS (ur `limit` (fv r1), r1) l next_i] 
>           }
>     ; Nothing | posEmpty r1 -> [ ((ur' ++ ur `limit` (fv r2)) , (Pair (i:is) r1' r2), renv) |  (ur', r1', renv) <- urPDeriv (ur `limit` (fv r1), r1) l next_i ] ++ (urPDeriv (ur `limit` (fv r2), r2) l next_i)
>               | otherwise   -> [ ((ur' ++ ur `limit` (fv r2)) , (Pair (i:is) r1' r2), renv) |  (ur', r1', renv) <- urPDeriv (ur `limit` (fv r1), r1) l next_i ]
>     }
> urPDeriv (ur, Choice (i:is) rs) l next_i = 
>    case lookup i ur of
>      { Just p ->  
>          case pderiv p l of
>          { [] -> []
>          ; ps -> let ur' = updateUR i (Choice dontcare ps) ur
>                  in concatMap (\ r -> urPDerivS (ur', r) l next_i) rs -- todo:move i:is to each r
>          }
>      ; Nothing -> concatMap (\ r -> urPDeriv (ur, r) l next_i) rs 
>      }
> urPDeriv (ur, Star (i:is) r) l next_i = 
>     case lookup i ur of 
>       { Just p -> 
>          case pderiv p l of
>          { [] -> []
>          ; ps -> let ur' = updateUR i (Choice dontcare ps) ur
>                  in [ (ur'', Pair (i:is) r' (Star (i:is) r), renv)  
>                        | (ur'', r', renv) <- urPDerivS (ur',r) l next_i ]
>          }
>       ; Nothing -> [ (ur', Pair (i:is) r' (Star (i:is) r), renv)  
>                        | (ur', r', renv) <- urPDeriv (ur,r) l next_i ]
>       }
> urPDeriv ur c next_i = error $ "unhandled input: " ++ (show ur) ++ "/" ++ (show c)


urPDeriv with Strong recommendation

> urPDerivS :: (UReq, Re) -> Char -> Int -> [(UReq, Re, REnv)]
> urPDerivS (ur, Eps (i:is)) l next_i
>   | i `inUR` ur = [ ((updateUR i r' ur), Eps [next_i], IM.singleton i [RApp (Ch [ next_i] l) Strong]) 
>                      | let r = fromJust (lookupUR i ur), r' <- pderiv r l ]
>   | otherwise   = [ (ur, (Eps [next_i]), IM.singleton i [RApp (Ch [ next_i] l) Strong]) ]
> urPDerivS (ur, (Ch (i:is) l)) l'  next_i = 
>   case lookup i ur of 
>     { Just r | l == l' -> [ ((updateUR i r' ur), (Eps (i:is)), IM.empty )
>                            | r' <- pderiv r l ]
>              | l /= l' -> [ ((updateUR i r' ur), (Eps (i:is)), IM.singleton i [RAdd (Ch [ next_i] l') Strong]) | r' <- pderiv r l]
>     ; Nothing | l == l' -> [ (ur, Eps (i:is), IM.empty ) ]
>               | l /= l' -> [ (ur, Eps (i:is), IM.singleton i [RAdd (Ch [ next_i] l') Strong] ) ] 
>     }
> urPDerivS (ur, Pair (i:is) r1 r2) l  next_i =
>    case lookup i ur of 
>     { Just p -> 
>         case pderiv p l of
>           { [] -> [] 
>           ; ps  | posEmpty r1 -> [ ((ur' ++ ur `limit` (fv r2) ++ [(i, Choice dontcare ps)]) , (Pair (i:is) r1' r2), renv) |  (ur', r1', renv) <- urPDerivS (ur `limit` (fv r1), r1) l next_i ] ++ (urPDerivS (ur `limit` (fv r2), r2) l next_i)
>                 | otherwise   -> [ ((ur' ++ ur `limit` (fv r2) ++ [(i, Choice dontcare ps)]) , (Pair (i:is) r1' r2), renv) |  (ur', r1', renv) <- urPDerivS (ur `limit` (fv r1), r1) l next_i ] 
>           }
>     ; Nothing | posEmpty r1 -> [ ((ur' ++ ur `limit` (fv r2)) , (Pair (i:is) r1' r2), renv) |  (ur', r1', renv) <- urPDerivS (ur `limit` (fv r1), r1) l next_i] ++ (urPDerivS (ur `limit` (fv r2), r2) l next_i)
>               | otherwise   -> [ ((ur' ++ ur `limit` (fv r2)) , (Pair (i:is) r1' r2), renv) |  (ur', r1', renv) <- urPDerivS (ur `limit` (fv r1), r1) l next_i]
>     }
> urPDerivS (ur, Choice (i:is) rs) l next_i = 
>    case lookup i ur of
>      { Just p ->  
>          case pderiv p l of
>          { [] -> []
>          ; ps -> let ur' = updateUR i (Choice dontcare ps) ur
>                  in concatMap (\ r -> urPDerivS (ur', r) l next_i) rs -- todo:move i:is to each r
>          }
>      ; Nothing -> concatMap (\ r -> urPDerivS (ur, r) l next_i) rs 
>      }
> urPDerivS (ur, Star (i:is) r) l next_i = 
>     case lookup i ur of 
>       { Just p -> 
>          case pderiv p l of
>          { [] -> []
>          ; ps -> let ur' = updateUR i (Choice dontcare ps) ur
>                  in [ (ur'', Pair (i:is) r' (Star (i:is) r), renv)  
>                        | (ur'', r', renv) <- urPDerivS (ur',r) l next_i]
>          }
>       ; Nothing -> [ (ur', Pair (i:is) r' (Star (i:is) r), renv)  
>                        | (ur', r', renv) <- urPDerivS (ur,r) l next_i]
>       }
> urPDerivS ur c next_i = error $ "unhandled input: " ++ (show ur)  ++ "/" ++ (show c)



return all labels annotation of a re

> fv :: Re -> [Int]
> fv (Eps is) = is
> fv (Ch is _) = is
> fv (Pair is r1 r2) = is ++ fv r1 ++ fv r2
> fv (Choice is rs)  = is ++ concatMap fv rs
> fv (Star is r) = is ++ fv r
> fv _ = []


retrict the user req based on a set of labels

> limit :: UReq -> [Int] -> UReq
> limit ur is = filter (\(i,_) -> i `elem` is) ur


``` 


```

applying REnv to a Re


> apply :: REnv -> Re -> Re 
> apply renv r = case getLabel r of 
>                {  (i:is) -> -- The first one is always the orginal label annotated to the regexp. The tail could contain those being collapsed because of pderiv op
>                  case IM.lookup i renv of 
>                    { Just rs -> let r' = apply' renv r
>                                     adds = map (\ (RAdd t _ ) -> t) $ filter isRAdd rs
>                                     apps = map (\ (RApp t _ ) -> apply renv t) $ filter isRApp rs
>                                     r''  = app r' apps 
>                                 in case adds of 
>                                    { (_:_) -> Choice (i:is) (r'':(map (\t -> annotate (i:is) t) adds))
>                                    ; [] -> r'' }
>                    ; Nothing -> apply' renv r
>                    }
>                ; [] -> error ("apply: getLabel is applied to a regular ex which has no label. " ++ (show r))
>                }

> apply' :: REnv -> Re -> Re
> apply' renv (Pair is r1 r2) = Pair is (apply renv r1) (apply renv r2)
> apply' renv (Choice is rs) = Choice is (map (apply renv) rs)
> apply' renv (Star is r) = Star is (apply renv r)
> apply' _ r = r

> app :: Re -> [Re] -> Re
> app r [] = r
> app r (t:ts) = let is = getLabel r 
>                in app (Pair is r (annotate is t)) ts


> combine :: REnv -> REnv -> REnv 
> combine renv1 renv2 = IM.unionWith (\x y -> nub (x ++ y)) renv1 renv2 

> extend :: REnv -> [Int] -> ROp -> REnv
> extend renv [] _ = renv
> extend renv (i:_) e@(RAdd r lvl) = -- we only care about the original label
>      case IM.lookup i renv of 
>       { Just rs | not (e `elem` rs) ->  IM.adjust (\_ -> rs++[RAdd r lvl]) i renv 
>                 | otherwise -> renv
>       ; Nothing -> IM.insert i [RAdd r lvl] renv
>       }





OLD STUFF: the norm and denorm are hard to explain


> {-

> refine :: [URPair] -> Doc -> [Re] 


```
 -------------------------------------------------------------------------------------------------- (Eps)
  { (\gamma_1, r_1), ..., (\gamma_n, r_n) } \models \epsilon : 
         { (\gamma_i, r_i) | (\gamma_i,r_i) \in { (\gamma_1, r_1), ..., (\gamma_n, r_n) } \wedge   
                              \epsilon \in \gamma_i (x) \forall x in \gamma_i \wedge 
                              \epsilon \in r_i }  ++ 
                              (\gamma_i,r_i?) \in { (\gamma_1, r_1), ..., (\gamma_n, r_n) } \wedge   
                              \epsilon \in \gamma_i (x) \forall x in \gamma_i \wedge 
                              \epsilon \not \in r_i }  

```

> refine urs [] = 
>   let urs' = filter (\ (URPair u r rec) -> allAccEps u ) urs 
>       (urs_rAccEps, urs_rNAccEps) = partition (\ (URPair u r rec) -> posEmpty r) urs'
>       rNAccEpsEps = map (\(URPair u r rec) -> let x = topLabel r in (Choice x [r, Eps x])) urs_rNAccEps
>       rAccEps = map (\ (URPair _ r _) -> r) urs_rAccEps
>   in rAccEps ++ rNAccEpsEps

```
   { (\gamma_1, r_1), ..., (\gamma_n, r_n) } / l =     { (\gamma_1', r_1'), ..., (\gamma_m', r_m') }
   
    { (\gamma_1', r_1'), ..., (\gamma_m', r_m') } \models v : { q_1', ... q_k' }
   
   { r_1, ..., r_n } ~>_norm  { (l_1, \bar{r}_1), ... (l,  \bar{r} ), ...,  (l_j, \bar{r}_j) } -- TODO: check why no need to takes in the user req? ANS: yes. no need, other monomials is not activated by the input lv.
  
    { (l_1, \bar{r}_1), ... (l,  \bar{q'} ), ...,  (l_j, \bar{r}_j) } ~>_denorm {q_1, ..., q_h }
 -------------------------------------------------------------------------------------------------- (Norm)
  { (\gamma_1, r_1), ..., (\gamma_n, r_n) } \models (lv) : {q_1, ..., q_h }
```

> refine urs (l:w) = 
>   let urs' = urPDeriv urs l 
>       qs'  = refine urs' w        
>       ms   = foldl (\m1 m2 -> m1 `unionLNF` m2) emptyLNF (map (\ (URPair _ r _) -> norm r) urs)  -- all the nfa states should be grouped into the same normal form, e.g. [ a, (a|b) ] ~> [a, b]
>       ms'  = combine ms l qs'
>       qs   = denorm ms'
>   in qs
>   where combine :: LNF -> Char -> [Re] -> LNF
>         combine = undefined

extracts the topmost level label

> -}

> {-

> topLabel :: Re -> [Int]
> topLabel (Eps x) = x
> topLabel (Ch x _) = x
> topLabel (Choice x _) = x
> topLabel (Pair x _ _) = x
> topLabel (Star x _) = x
> topLabel Phi = dontcare


normalization
  $p \norm m1 | ... | mn$  
                 
     where m_i denotes the monomial of shape (l_i, [r1,...,rn])

de-normalization
  $ m1 | ... | mn \denorm p$ 


1) l, \epsilon_i r -> li r
2) { r1 r, r2 r } => (r1|r2) r
3)  r_i (r'_i)*_j and r_i \subseteq r_i' ->    r_i*_j    () \in lnf 
                       ^^^^^^^^^^^^^^^^^^      r_i+_j    otherwise    -- this or directly update the l_i to (l|l')_i? for all location of i in r?
4) (r*|\epsilon) r' -> r* r'                 
    

The linear normal form


lnf ::= { (l1,\bar{r1}), ... , (ln, \bar{rn}) } U {\eps}  ||
        { (l1,\bar{r1}), ... , (ln, \bar{rn}) } 

> data LNF = WithEps [Int] ( M.Map Char [Re] -- Maping l -> [r]
>                          , M.Map Re [Re] ) -- Mapping r* -> prefix 
>          | WithoutEps [Int] ( M.Map Char [Re] -- Mapping l -> [r]
>                             , M.Map Re [Re] ) -- Mapping r* -> prefix
>           deriving Show

what is in addition is the dictionary that maps the trailing r* back to the prefix for all the monomials. It will be used to 
denormalization


> emptyLNF = WithoutEps [] (M.empty, M.empty)

> unionLNF :: LNF -> LNF -> LNF 
> unionLNF = undefined



norm r = if () \in r then (norm' r) ++ { () }  else (norm' r)

> norm :: Re -> LNF                            
> norm Phi = error "applying norm to Phi"
> norm r | posEmpty r = WithEps x (norm' x r)
>        | otherwise  = WithoutEps x (norm' x r)
>   where x = getLabel r
              

norm' r = groupBy (eq . last) [(l, r') | l \in \sigma(r), r' \in pderiv r l]

> norm' :: [Int] -> Re -> (M.Map Char [Re], M.Map Re [Re])
> norm' x r = let ms = [ (l, r') | l <- sigma r, r' <- pderiv r l ]
>             in (foldl (\m (l,r) -> upsert l [r] (++) m) M.empty ms, foldl (\m (r,l) -> upsert r [l] (++) m) M.empty (map (\(l,r) -> (last_ r, Pair x (Ch x l) (init_ r))) ms))

last_ returns the right most re in a sequence of Re

> last_ :: Re -> Re 
> last_ (Pair x r1 r2) = last_ r2
> last_ r = r

> init_ :: Re -> Re
> init_ (Pair x r1 r2) = let r2' = (init_ r2)
>                        in case r2' of { Eps _ -> r1; _ -> Pair x r1 r2' }
> init_ r = Eps dontcare

append_ appends two Re(s) by sequence

> append_ :: [Int] -> Re -> Re -> Re
> append_ _ (Pair y r1 r2) r3 = Pair y r1 (append_ y r2 r3)
> append_ x r1 r2 = Pair x r1 r2

> upsert :: Ord k => k -> v -> (v -> v -> v) -> M.Map k v -> M.Map k v
> upsert k v f m = case M.lookup k m of 
>                  { Just v' -> M.adjust (\_ -> f v' v) k m 
>                  ; Nothing -> M.insert k v m }

> lookupMN :: Char -> LNF -> Maybe [Re]

> lookupMN c (WithEps x (m1,m2)) = M.lookup c m1
> lookupMN c (WithoutEps x (m1,m2)) = M.lookup c m1

> updateMN :: Char -> [Re] -> LNF -> LNF
> updateMN c rs (WithEps x (m1,m2)) = 
>    let ps = map (\r -> (last_ r, Pair x (Ch x c) (init_ r))) rs   -- the tails and the head (prefix + label)
>    in WithEps x (M.adjust (\_ -> rs) c m1, foldl (\m (t,h) -> upsert t [h] (++) m) m2 ps)  -- the subfix r' might not be in m2
> updateMN c rs (WithoutEps x (m1,m2)) = 
>    let  ps = map (\r -> (last_ r, Pair x (Ch x c) (init_ r))) rs   -- the tails and the head (prefix + label)
>    in WithoutEps x (M.adjust (\_ -> rs) c m1, foldl (\m (t,h) -> upsert t [h] (++) m) m2 ps)  -- the subfix r' might not be in m2

> insertMN :: Char -> [Re] -> LNF -> LNF
> insertMN c rs (WithEps x (m1,m2)) = 
>    let ps = map (\r -> (last_ r, Pair x (Ch x c) (init_ r))) rs   -- the tails and the head (prefix + label)  
>    in WithEps x (M.insert c rs m1, foldl (\m (t,h) -> upsert t [h] (++) m) m2 ps) 
> insertMN c rs (WithoutEps x (m1,m2)) = 
>    let ps = map (\r -> (last_ r, Pair x (Ch x c) (init_ r))) rs   -- the tails and the head (prefix + label)  
>    in WithoutEps x (M.insert c rs m1, foldl (\m (t,h) -> upsert t [h] (++) m) m2 ps)

> singleton :: [Int] -> Doc -> Re 
> singleton x cs = foldr (\l r -> Pair x (Ch x l) r) (Eps x) cs


return a choice if the list is non-singleton

> mkChoice :: [Int] -> [Re] -> Re 
> mkChoice x [r] = r
> mkChoice x rs = Choice x rs

denorm (\bar{m}|()) = let (pluses, nonpluses) = splitBy isPlusMonomial $ denorm' \bar{m}                           
                      in [ (mkStar plus) | plus <- pluses ] ++ nonpluses
                          
denorm \bar{m} = let (pluses, nonpluses) = splitBy isPlusMonomial $ denorm' \bar{m}
                 in [ (mkPlus plus) | plus <- pluses ]  ++ nonpluses


> denorm :: LNF -> [Re]
> denorm (WithEps x (m1,m2)) = 
>    let (plusMonoGrp, nonPlusMonoGrp) = part m2 
>        ps = map mkStar (M.toList plusMonoGrp)         
>        nps = map (\(tl, its) -> append_ x (mkChoice x its) tl) (M.toList nonPlusMonoGrp)
>    in (ps ++ nps)
> denorm (WithoutEps x (m1,m2)) = 
>    let (plusMonoGrp, nonPlusMonoGrp) = part m2 
>        ps = map mkPlus (M.toList plusMonoGrp)         
>        nps = map (\(tl, its) -> append_ x (mkChoice x its) tl) (M.toList nonPlusMonoGrp)
>    in (ps ++ nps)


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


> -}
