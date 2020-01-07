module Properties

%access export

-- Algebraic Properties --------------------------
public export
interface Closed (A : Type) where
  f : A -> A -> A

interface (Closed A) => Associative A where
  assoc_prf : (a, b, c : A) -> (f a (f b c) = f (f a b) c)

interface (Closed A) => Commutative A where
  commut_prf : (a, b : A) -> (f a b = f b a)

interface (Associative A) => Monoid' A where
  idElm      : A
  monoid_prf : (a : A) -> (f idElm a = a)

interface (Monoid' A) => Group A where
  group_prf : (a : A) -> (b : A ** (f a b = Properties.idElm))

interface (Group A , Commutative A) => Abelian A where
 ----------------------------------------------------------
