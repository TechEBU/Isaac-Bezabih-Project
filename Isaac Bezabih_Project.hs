Require Import String.
Require Import ZArith.

Inductive Critical :=
  Crit : string -> Critical.

Inductive FooT :=
  Foo : Z -> Critical -> FooT.

Inductive BarT :=
  Bar : string -> Critical -> BarT.

Lemma convertIsGood : forall (f : FooT) (b : BarT),
  goodConvert f = b -> critF f = critB b.
Proof.
  intros. 
  destruct f. destruct b.
  unfold goodConvert in H. simpl.
  inversion H. reflexivity.
Qed.

Extraction Language Haskell.
Extract Constant ascii_of_Z => "Prelude.show".  (* obviously, all sorts of unsafe and incorrect behavior can be introduced by your extraction *)
Extract Inductive string => "Prelude.String" ["[]" ":"]. Print positive.
Extract Inductive positive => "Prelude.Integer" ["`Data.Bits.shiftL` 1 + 1" "`Data.Bits.shiftL` 1" "1"].
Extract Inductive Z => "Prelude.Integer" ["0" "" ""].

Extraction "so.hs" goodConvert critF critB.

module So where

import qualified Prelude

data Bool =
   True
 | False

data Ascii0 =
   Ascii Bool Bool Bool Bool Bool Bool Bool Bool

type Critical =
  Prelude.String
  -- singleton inductive, whose constructor was crit

data FooT =
   Foo Prelude.Integer Critical

data BarT =
   Bar Prelude.String Critical

critF :: FooT -> Critical
critF f =
  case f of {
   Foo z c -> c}

critB :: BarT -> Critical
critB b =
  case b of {
   Bar s c -> c}

ascii_of_Z :: Prelude.Integer -> Prelude.String
ascii_of_Z z =
  []

goodConvert :: FooT -> BarT
goodConvert foo =
  case foo of {
   Foo n c -> Bar (ascii_of_Z n) c}

Can we run it?? Does it work?

> critB $ goodConvert (Foo 32 "hi")
"hi"

