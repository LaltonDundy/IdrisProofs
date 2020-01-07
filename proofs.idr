module Proofs

import Language.Reflection
import Language.Reflection.Elab
import Pruviloj
import Pruviloj.Induction

-- properties.idr
import properties

%default total
%language ElabReflection

-- Function application AKA Modens Ponens
modens : (a, b : Type)     -> 
         (arg : a)         -> -- argument
         (f : (a -> b))    -> -- function/implication/morphism
         b                    -- resulting value
modens = %runElab 
                (do 
                    repeatUntilFail intro'
                    exact (RApp (Var `{{f}}) (Var `{{arg}})))

-- Left Projection
proj1 :  (a, b : Type)       -> 
         (prod : Pair a b)   -> -- Product Type/Logical Conjunction
         a                      -- Left Projection
proj1 = %runElab (
        do
          intro'
          intro'
          exact   (RApp 
                    (RApp (Var `{Prelude.Basics.fst}) 
                            (Var `{{a}})) 
                            (Var `{{b}})) 
      )

-- Right Projection
proj2 :  (a, b : Type)       -> 
         (prod : Pair a b)   -> -- Product Type/Logical Conjunction
         b                      -- Right Projection
proj2 = %runElab (
        do
          intro'
          intro'
          exact  (RApp 
                    (RApp (Var `{Prelude.Basics.snd}) 
                            (Var `{{b}})) 
                            (Var `{{a}})) 
      )

-- Left Injection
inj1 : (a, b : Type)  -> 
       (caseA : a)    -> -- injection of type 'a'
       Either a b        -- resulting Sum Type instance / Logical OR
inj1 = %runElab 
          (do intro'
              intro'
              exact   (RApp 
                        (RApp (Var `{Left}) 
                          (Var `{{b}})) 
                          (Var `{{a}})) 
           )

-- Right Injection
inj2 : (a, b : Type)  -> 
       (caseB : b)    -> -- injection of type 'b'
       Either a b        -- resulting Sum Type instance / Logical OR
inj2 = %runElab 
          (do intro'
              intro'
              exact   (RApp 
                        (RApp (Var `{Right}) 
                          (Var `{{b}})) 
                          (Var `{{a}})) 
          )

-- Isomorphism  <~~>
-- ||| This will hopefully be easier to use/prove than traditional equality for some important cases
iso : (a, b : Type)  ->  
      (f : (a -> b)) ->  -- Function Left to Right
      (g : (b -> a)) ->  -- Function Right to Left
      Type
iso a b f g = (proofA : a)   -> -- forall instances of 'a'
              (proofB : b)   -> -- forall instances of 'b'
              (Pair 
                ( g (f proofA) = proofA ) -- Left  Identity
                ( f (g proofB) = proofB ) -- Right Identity
               )

-- Distrabution (a, b | c) <~~> ((a , b) | (a , c))
-- ||| Couln't figure out how to do this using the Elaborator yet
dist : (a, b, c : Type) -> 
       (DPair (Pair a (Either b c) -> (Either (Pair a b) (Pair a c))) (\f =>          -- there exists f such that ...
              (DPair ((Either (Pair a b) (Pair a c)) -> (Pair a (Either b c))) (\g => -- there exists g such that ...
                    iso (Pair a (Either b c)) (Either (Pair a b) (Pair a c)) f g      -- (a, b | c) isomorphic to (a , b) | (a , c)
              )))) 
dist a b c = MkDPair f' . -- proof of f
             MkDPair g' $ -- proof of g
              (\arg1 =>   -- Given Every (a , b | c)
              (\arg2 =>   -- Given Every (a , b) | (a ,c)
                     (case arg1 of
                            (a, Left b)  => (case arg2 of
                                              (Left  (x,y)) => (Refl, Refl)
                                              (Right (x,y)) => (Refl, Refl))
                            (a, Right b) => (case arg2 of
                                              (Left  (x,y)) => (Refl, Refl) 
                                              (Right (x,y)) => (Refl, Refl)))))
              where
                f' : (Pair a (Either b c) -> (Either (Pair a b) (Pair a c)))
                f' arg = case arg of
                            (fs, Left  sn) => Left  (fs, sn)
                            (fs, Right sn) => Right (fs, sn)
                g' : ((Either (Pair a b) (Pair a c)) -> (Pair a (Either b c)))
                g' arg = case arg of
                            Left  (fs, sn) => (fs, Left  sn) 
                            Right (fs, sn) => (fs, Right sn) 

-- Composition
comp : (a, b, c : Type) ->
       (f : (a -> b))   -> 
       (g : (b -> c))   ->
       (arg : a) -> c
comp = %runElab (do 
                repeatUntilFail intro'
                exact (RApp (Var `{{g}}) (RApp (Var `{{f}}) (Var `{{arg}}))))

-- Natural Numbers
data N : Type where
  Z' : N
  S' : N -> N

-- Addition for natural numbers
add : N -> N -> N
add  Z'      n = n
add (S' n1) n2 = S' (add n1 n2)

implementation Closed N where
  f = add

implementation Associative N where
  assoc_prf = %runElab  (do repeatUntilFail intro'
                            induction (Var `{{a}})
                            compute
                            search
                            compute
                            attack
                            intro `{{x}}
                            intro `{{hy}}
                            rewriteWith (Var `{{hy}})
                            search
                            solve)

implementation Monoid' N where
  idElm = Z'
  monoid_prf = %runElab (do intros
                            search)

implementation Commutative N where
  commut_prf Z'     b = ?commut1
  commut_prf (S' a) b = ?commut2

-- Commutative Base Case
Proofs.commut1 = %runElab (do intro'
                              induction $ Var `{{b}}
                              compute
                              reflexivity
                              compute
                              attack
                              x  <- gensym "x"
                              hy <- gensym "hy"
                              intro x
                              intro hy
                              rewriteWith $ Var hy
                              reflexivity
                              solve)

-- Commutative Induction Step
Proofs.commut2 = %runElab (do intro'
                              intro'
                              induction $ Var `{{b}}
                              compute
                              let com1 = RApp (Var `{commut1}) (Var `{{a}})
                              attack
                              rewriteWith com1
                              reflexivity
                              solve
                              compute
                              attack
                              intro `{{x}}
                              intro `{{hy}}
                              rewriteWith $ Var `{{hy}}
                              attack
                              hyRev <- symmetryAs (Var `{{hy}}) "hyRev"
                              induction $ Var `{{a}}
                              compute
                              reflexivity
                              compute
                              attack
                              intro `{{x1}}
                              intro `{{hy1}}
                              rewriteWith $ Var `{{hy1}}
                              reflexivity
                              solve
                              solve
                              solve)
