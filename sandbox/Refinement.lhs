> {-# LANGUAGE GADTs #-}

The regular expression refinement algorithm

Inspired by the type checking system and type inference algorithm found in programming language research communities. \cite{TODO}

= Type checking and Type inference algorithm =

== Type checking judgement ==
$\gamma \vdash e : t$ 
Given the type environemnt $\gamma$, the program expression e and the type $t$, the above is deducable if $e$ has type $t$ under the type environment $\gamma$

Note that the type checking is a relation, where $\gamma$, $e$ and $t$ are the inputs.

== Type inference judgement == 

$\gamma \models e : t$

Given the type environment \gamma and the program expression e the algorithm reconstructs the type t.

Note that the type inference is considered an function, where \gamma and e are the inputs.

=== Type inference correctness === 

$\gamma \models e : t$ 
implies 
$\gamma \vdash e : t$ 




= Regular expression debugging and reconstruction =

== The connection == 

Pointed out the XDuce work, we consider the correspondence between the program expression $e$ and the document $d$,
the type $t$ and the regular expression $r$.

 * The word problem  $d \in r$ corresponds to the type checking problem.

== The difference == 

 * The matching problem 

 $$ d \in r \Longrightarrow \Delta $$ 

where r is annotated with label at each AST level. $\Delta$ maps labels to sub-matches.


== The mechanism == 

We use derivative (or partial derivative) operations to implement the word problem and the sub matching problem. See our recent papers (PPDP 12 )


== The debugging algorithm == 

Refer to the PDDebug.lhs

== The Refinement checking judgement == 

> module Main where

> import qualified Data.Map as M

=== The problem === 

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
>  deriving Show


> class PosEmpty t where
>   posEmpty :: t -> Bool


> instance PosEmpty Re where
>   posEmpty (Eps _)        = True
>   posEmpty (Choice _ rs)  = any posEmpty rs
>   posEmpty (Pair _ r1 r2) = posEmpty r1 && posEmpty r2
>   posEmpty (Star _ _)     = True
>   posEmpty (Ch _ _)       = False
>   posEmpty Phi            = False


> class Deriv t where
>   deriv :: t -> Char -> t

> instance Deriv Re where
>   deriv (Eps _) _ = Phi
>   deriv (Choice x rs) l = Choice x (map (\r -> deriv r l) rs)
>   deriv (Pair x r1 r2) l | posEmpty r1 = Choice x [Pair x (deriv r1 l) r2, deriv r2 l]
>                          | otherwise = Pair x (deriv r1 l) r2
>   deriv (Star x r) l = Pair x (deriv r l) (Star x r)
>   deriv (Ch x c) l | c == l = (Eps x)
>                    | otherwise = Phi
>   deriv Phi _ = Phi


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


=== The Replacement Relation ===
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






=== The Refinement Algorithm ===

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

  r^x \norm (l1^x,p1)|...| (l^x,pi) |...|(ln^x,pn)
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
>                     ; let ms' = updateMN l pi' ms 
>                     ; return (denorm ms')
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




==== $p \norm m1 | ... | mn$ and $ m1 | ... | mn \denorm p$ ====


> data Monomials = WithEps [M.Map Char Re] -- group by common second components
>                | WithoutEps [M.Map Char Re]

norm r = if () \in r then (norm' r) | ()  else (norm' r)

                            
> norm :: Re -> Monomials                            
> norm r | posEmpty r = WithEps (norm' r)
>        | otherwise  = WithoutEps (norm' r)

norm' r = groupBy (eq . snd) [(l, r/l) | l \in \sigma(r)]

> norm' :: Re -> [M.Map Char Re]
> norm' = undefined 

> lookupMN :: Char -> Monomials -> Maybe Re
> lookupMN = undefined

> updateMN :: Char -> Re -> Monomials -> Monomials
> updateMN = undefined

> insertMN :: Char -> Re -> Monomials -> Monomials
> insertMN = undefined

> singleton :: Int -> Doc -> Re 
> singleton = undefined

> denorm :: Monomials -> Re
> denorm = undefined

                          
denorm (\bar{m}|()) = let (pluses, nonpluses) = splitBy isPlusMonomial $ denorm' \bar{m}                           
                      in [ (mkStar plus) | plus <- pluses ] ++ nonpluses
                          
denorm \bar{m} = let (pluses, nonpluses) = splitBy isPlusMonomial $ denorm' \bar{m}
                 in [ (mkPlus plus) | plus <- pluses ]  ++ nonpluses
                          
denorm' \bar{m} = groupBy (eq . snd) [(l, r/l) | l \in \sigma(r)]

isPlusMonomial (l,p) = l \in (choiceToList p)

mkStar ms = let fs = map fst ms  
                (Star r) = snd (head ms)
            in if (sort fs) == (sort (choiceToList r)) then (Star r) else ms

mkPlus ms = let fs = map fst ms  
                (Star r) = snd (head ms)
            in if (sort fs) == (sort (choiceToList r)) then (r, (Star r)) else ms
                          

