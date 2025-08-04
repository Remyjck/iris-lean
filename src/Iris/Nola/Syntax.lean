import Iris.BI
import Iris.Algebra.Own
import Iris.Std.Namespaces

inductive cif.binsel where
| /- Conjunction -/ and
| /- Disjunction -/ or
| /- Implication -/ imp
| /- Separating conjunction -/ sep
| /- Magic wand -/ wand

inductive cif.unsel where
| /- Plainly -/ plain
| /- Persistently -/ pers
| /- Basic update -/ bupd
| /- Except-0 -/ except0

inductive cif.{u} (FF : Iris.GFunctors) : Type (u + 1) where
| all {A : Type u} (Φ : A → cif FF)
| ex  {A : Type u} (Φ : A → cif FF)
| bin (s : cif.binsel) (P : cif FF) (Q : cif FF)
| un  (s : cif.unsel) (P : cif FF)
| pure (P : Prop)
| later (iP : Iris.IProp FF)
| inv (N : Namespace) (fml : cif FF)
| own {A : Type} [Iris.CMRA A] [inG FF A] (a : A)

instance : Nonempty (cif FF) := ⟨ cif.pure True ⟩

def liftCif.{u, v} (P : cif.{u} FF) : cif.{max u v} FF :=
  match P with
  | @cif.all _ A Φ =>
      -- We need to lift the domain type A from Type u to Type (max u v)
      cif.all (fun (a : ULift.{max u v, u} A) => liftCif (Φ a.down))
  | @cif.ex _ A Φ =>
      cif.ex (fun (a : ULift.{max u v, u} A) => liftCif (Φ a.down))
  | cif.bin s P Q =>
      cif.bin s (liftCif P) (liftCif Q)
  | cif.un s P =>
      cif.un s (liftCif P)
  | cif.pure P =>
      cif.pure P
  | cif.later iP =>
      cif.later iP
  | cif.inv N fml =>
      cif.inv N (liftCif fml)
  | cif.own a =>
      cif.own a

namespace cif

def wandIff {FF} (P Q : cif FF) : cif FF :=
  cif.bin binsel.and
    (cif.bin binsel.wand P Q)
    (cif.bin binsel.wand Q P)

def plain (P : cif FF) : cif FF := cif.un unsel.plain P
def pers (P : cif FF) : cif FF := cif.un unsel.pers P
def bupd (P : cif FF) : cif FF := cif.un unsel.bupd P
def except0 (P : cif FF) : cif FF := cif.un unsel.except0 P

def and (P Q : cif FF) : cif FF := bin cif.binsel.and P Q
def and_lift.{u, v} (P : cif.{u} FF) (Q : cif.{v} FF) : cif.{max u v} FF :=
  bin cif.binsel.and (liftCif P) (liftCif Q)

def or (P Q : cif FF) : cif FF := cif.bin binsel.or P Q

def imp (P Q : cif FF) : cif FF := bin cif.binsel.imp P Q
def imp_lift.{u, v} (P : cif.{u} FF) (Q : cif.{v} FF) : cif.{max u v} FF :=
  bin cif.binsel.imp (liftCif P) (liftCif Q)

def sep (P Q : cif FF) : cif FF := cif.bin binsel.sep P Q
def wand (P Q : cif FF) : cif FF := cif.bin binsel.wand P Q


/- [∀ p, ⌜Φ p⌝ -> p] -/
def sForall.{u} (Φ : cif.{u} FF → Prop) : cif.{u + 1} FF :=
  all (fun (p : cif.{u} FF) =>
    imp
      (pure (Φ p))
      (liftCif.{u,u+1} p))

/- [∃ p, ⌜Φ p⌝ ∧ p] -/
def sExists (Φ : cif.{u} FF → Prop) : cif.{u + 1} FF :=
  ex (fun p =>
    and
      (pure (Φ p))
      (liftCif.{u,u+1} p))

def all' {α} (P : α → cif FF) : cif FF := sForall (fun p => ∃ a, P a = p)
def ex' {α} (P : α → cif FF) : cif FF := sExists (fun p => ∃ a, P a = p)

inductive dist {FF} : Nat -> cif FF -> cif FF -> Prop
| bin : ∀ {n} {s s' : binsel} {P Q P' Q' : cif FF},
    s = s' ->
    dist n P P' ->
    dist n Q Q' ->
    dist n (cif.bin s P Q) (cif.bin s' P' Q')
| un : ∀ {n} {s s' : unsel} {P P' : cif FF},
    s = s' ->
    dist n P P' ->
    dist n (cif.un s P) (cif.un s' P')
| all : ∀ {n} {A : Type} {Φ Φ' : A -> cif FF},
    (∀ a, dist n (Φ a) (Φ' a)) ->
    dist n (cif.all Φ) (cif.all Φ')
| ex : ∀ {n} {A : Type} {Φ Φ' : A -> cif FF},
    (∀ a, dist n (Φ a) (Φ' a)) ->
    dist n (cif.ex Φ) (cif.ex Φ')
| pure : ∀ {n} {P P' : Prop},
    (P <-> P') ->
    dist n (cif.pure P) (cif.pure P')
| later : ∀ {n} {iP iP' : Iris.IProp FF},
    Iris.OFE.DistLater n iP iP' ->
    dist n (cif.later iP) (cif.later iP')
| inv : ∀ {n} {N N' : Namespace} {fml fml' : cif FF},
    (N = N') ->
    (dist n fml fml') ->
    dist n (cif.inv N fml) (cif.inv N' fml')
| own : ∀ {n} {A : Type} [Iris.CMRA A] [inG FF A]
    {a a' : A},
    (a = a') ->
    dist n (@cif.own _ A _ _ a) (@cif.own FF A _ _ a')

@[refl]
theorem dist.refl {n : Nat} {f : cif FF} : dist n f f := by
  induction f <;> try constructor <;> try assumption
  all_goals
    try rfl

@[symm]
theorem dist.symm {n : Nat} {f f' : cif FF} (H : dist n f f') : dist n f' f := by
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

theorem pure_dist_inv (P : Prop) (f : cif FF) n :
  dist n (cif.pure P) f ->
  ∃ P', f = cif.pure P' ∧ (P <-> P') := by
  rintro ⟨P', rfl, H⟩
  rename Prop => P'
  exists P'

theorem dist.trans {n : Nat} {f f' f'' : cif FF}
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

def equiv (f f' : cif FF) := ∀ n, dist n f f'

instance : Iris.OFE (cif FF) where
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

end cif
