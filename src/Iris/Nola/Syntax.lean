import Iris.BI
import Iris.Algebra.Own
import Iris.Std.Namespaces

inductive Fml.binsel where
| /- Conjunction -/ and
| /- Disjunction -/ or
| /- Implication -/ imp
| /- Separating conjunction -/ sep
| /- Magic wand -/ wand

inductive Fml.unsel where
| /- Plainly -/ plain
| /- Persistently -/ pers
| /- Basic update -/ bupd
| /- Except-0 -/ except0

inductive Fml.{u} (FF : Iris.GFunctors) : Type (u + 1) where
| all {A : Type u} (Φ : A → Fml FF)
| ex  {A : Type u} (Φ : A → Fml FF)
| bin (s : Fml.binsel) (P : Fml FF) (Q : Fml FF)
| un  (s : Fml.unsel) (P : Fml FF)
| pure (P : Prop)
| later (iP : Iris.IProp FF)
| inv (N : Namespace) (fml : Fml FF)
| own {A : Type} [Iris.CMRA A] [inG FF A] (a : A)

instance : Nonempty (Fml FF) := ⟨ Fml.pure True ⟩

def liftFml.{u, v} (P : Fml.{u} FF) : Fml.{max u v} FF :=
  match P with
  | @Fml.all _ A Φ =>
      -- We need to lift the domain type A from Type u to Type (max u v)
      Fml.all (fun (a : ULift.{max u v, u} A) => liftFml (Φ a.down))
  | @Fml.ex _ A Φ =>
      Fml.ex (fun (a : ULift.{max u v, u} A) => liftFml (Φ a.down))
  | Fml.bin s P Q =>
      Fml.bin s (liftFml P) (liftFml Q)
  | Fml.un s P =>
      Fml.un s (liftFml P)
  | Fml.pure P =>
      Fml.pure P
  | Fml.later iP =>
      Fml.later iP
  | Fml.inv N fml =>
      Fml.inv N (liftFml fml)
  | Fml.own a =>
      Fml.own a

namespace Fml

def wandIff {FF} (P Q : Fml FF) : Fml FF :=
  Fml.bin binsel.and
    (Fml.bin binsel.wand P Q)
    (Fml.bin binsel.wand Q P)

def plain (P : Fml FF) : Fml FF := Fml.un unsel.plain P
def pers (P : Fml FF) : Fml FF := Fml.un unsel.pers P
def bupd (P : Fml FF) : Fml FF := Fml.un unsel.bupd P
def except0 (P : Fml FF) : Fml FF := Fml.un unsel.except0 P

def and (P Q : Fml FF) : Fml FF := bin Fml.binsel.and P Q
def and_lift.{u, v} (P : Fml.{u} FF) (Q : Fml.{v} FF) : Fml.{max u v} FF :=
  bin Fml.binsel.and (liftFml P) (liftFml Q)

def or (P Q : Fml FF) : Fml FF := Fml.bin binsel.or P Q

def imp (P Q : Fml FF) : Fml FF := bin Fml.binsel.imp P Q
def imp_lift.{u, v} (P : Fml.{u} FF) (Q : Fml.{v} FF) : Fml.{max u v} FF :=
  bin Fml.binsel.imp (liftFml P) (liftFml Q)

def sep (P Q : Fml FF) : Fml FF := Fml.bin binsel.sep P Q
def wand (P Q : Fml FF) : Fml FF := Fml.bin binsel.wand P Q

inductive dist {FF} : Nat -> Fml FF -> Fml FF -> Prop
| bin : ∀ {n} {s s' : binsel} {P Q P' Q' : Fml FF},
    s = s' ->
    dist n P P' ->
    dist n Q Q' ->
    dist n (Fml.bin s P Q) (Fml.bin s' P' Q')
| un : ∀ {n} {s s' : unsel} {P P' : Fml FF},
    s = s' ->
    dist n P P' ->
    dist n (Fml.un s P) (Fml.un s' P')
| all : ∀ {n} {A : Type} {Φ Φ' : A -> Fml FF},
    (∀ a, dist n (Φ a) (Φ' a)) ->
    dist n (Fml.all Φ) (Fml.all Φ')
| ex : ∀ {n} {A : Type} {Φ Φ' : A -> Fml FF},
    (∀ a, dist n (Φ a) (Φ' a)) ->
    dist n (Fml.ex Φ) (Fml.ex Φ')
| pure : ∀ {n} {P P' : Prop},
    (P <-> P') ->
    dist n (Fml.pure P) (Fml.pure P')
| later : ∀ {n} {iP iP' : Iris.IProp FF},
    Iris.OFE.DistLater n iP iP' ->
    dist n (Fml.later iP) (Fml.later iP')
| inv : ∀ {n} {N N' : Namespace} {fml fml' : Fml FF},
    (N = N') ->
    (dist n fml fml') ->
    dist n (Fml.inv N fml) (Fml.inv N' fml')
| own : ∀ {n} {A : Type} [Iris.CMRA A] [inG FF A]
    {a a' : A},
    (a = a') ->
    dist n (@Fml.own _ A _ _ a) (@Fml.own FF A _ _ a')

@[refl]
theorem dist.refl {n : Nat} {f : Fml FF} : dist n f f := by
  induction f <;> try constructor <;> try assumption
  all_goals
    try rfl

@[symm]
theorem dist.symm {n : Nat} {f f' : Fml FF} (H : dist n f f') : dist n f' f := by
  induction H with
  | bin heq Hdist1 Hdist2 =>
    apply (dist.bin (by symm; assumption)) <;> assumption
  | un heq Hdist =>
    apply (dist.un (by symm; assumption)) <;> assumption
  | all hdist =>
    apply dist.all; assumption
  | ex hdist =>
    apply dist.ex; assumption
  | pure heq => rename_i P P'; apply (@dist.pure _ _ P' P); symm; assumption
  | later Hdist =>
    apply (dist.later (by symm; assumption)) <;> assumption
  | inv heq Hdist =>
    apply (dist.inv (by symm; assumption)) <;> assumption
  | own heq =>
    apply dist.own; symm; assumption

theorem pure_dist_inv (P : Prop) (f : Fml FF) n :
  dist n (Fml.pure P) f ->
  ∃ P', f = Fml.pure P' ∧ (P <-> P') := by
  rintro ⟨P', rfl, H⟩
  rename Prop => P'
  exists P'

theorem dist.trans {n : Nat} {f f' f'' : Fml FF}
    (H1 : dist n f f') (H2 : dist n f' f'') : dist n f f'' := by
  induction H1 generalizing f'' with
  | bin heq Hdist1 Hdist2 =>
    cases H2 with | bin heq' Hdist1'
    apply (dist.bin (heq.trans heq'))
    (expose_names; exact a_ih Hdist1')
    (expose_names; exact a_ih_1 h)
  | un heq Hdist =>
    cases H2 with | un heq' Hdist'
    apply (dist.un (heq.trans heq')); (expose_names; exact a_ih Hdist')
  | all hdist =>
    cases H2 with | all hdist'
    apply dist.all; intro a; (expose_names; exact a_ih a (hdist' a))
  | ex hdist =>
    cases H2 with | ex hdist'
    apply dist.ex; intro a; (expose_names; exact a_ih a (hdist' a))
  | pure heq =>
    cases H2 with | pure heq'
    apply dist.pure; apply heq.trans heq'
  | later Hdist =>
    cases H2 with | later Hdist'
    apply dist.later; apply Iris.OFE.DistLater.trans Hdist Hdist'
  | inv heq Hdist =>
    cases H2 with | inv heq' Hdist'
    apply (dist.inv (heq.trans heq')); (expose_names; exact a_ih Hdist')
  | own heq =>
    cases H2 with | own heq'
    apply dist.own (heq.trans heq')

def equiv (f f' : Fml FF) := ∀ n, dist n f f'

instance : Iris.OFE (Fml FF) where
  Equiv := equiv
  Dist := dist
  dist_eqv := ⟨ fun x => @dist.refl _ _ x, dist.symm, dist.trans ⟩
  equiv_dist := ⟨ id, fun Hdist n=> (Hdist n)⟩
  dist_lt := by
    intros n P Q m Hdist Hlt
    induction Hdist with
    | bin heq Hdist1 Hdist2 =>
      apply (dist.bin heq) <;> assumption
    | un heq Hdist =>
      apply (dist.un heq) <;> assumption
    | all hdist =>
      apply dist.all; intro a
      (expose_names; exact a_ih a)
    | ex hdist =>
      apply dist.ex; intro a
      (expose_names; exact a_ih a)
    | pure heq =>
      rename_i P P'
      apply (@dist.pure _ _ P P' heq)
    | later Hdist =>
      apply dist.later; intros m' Hlt'
      apply Iris.OFE.DistLater.dist_lt Hdist (Nat.lt_trans Hlt' Hlt)
    | inv heq Hdist =>
      apply (dist.inv heq)
      (expose_names; exact a_ih)
    | own heq =>
      apply dist.own; exact heq

end Fml
