import Iris.BI
import Iris.Algebra.Own
import Iris.Std.Namespaces

inductive cif_binsel where
| /- Conjunction -/ cifs_and
| /- Disjunction -/ cifs_or
| /- Implication -/ cifs_imp
| /- Separating conjunction -/ cifs_sep
| /- Magic wand -/ cifs_wand

inductive cif_unsel where
| /- Plainly -/ cifs_plain
| /- Persistently -/ cifs_pers
| /- Basic update -/ cifs_bupd
| /- Except-0 -/ cifs_except0

set_option pp.universes true

inductive cif (FF : Iris.GFunctors) : Type (u + 1) where
| /- Universal quantifier -/ cifs_all (A : Type u) (Φ : A -> cif FF)
| /- Existential quantifier -/ cifs_ex (A : Type u) (Φ : A -> cif FF)
| /- Binary operator -/ cifs_bin (s : cif_binsel) (P : cif FF) (Q : cif FF)
| /- Unary operator -/ cifs_un (s : cif_unsel) (P : cif FF)
| /- Pure proposition -/ cifs_pure (P : Prop)
| /- Later -/ cifs_later (iP : Iris.IProp FF)
| /- Invariant -/ cifs_inv (N : Namespace) (fml : cif FF)
| /- Custom selector -/ cifs_own [Iris.CMRA A] [inG FF A] (a : A)


#print cif

open ULift

mutual
  def lift_cif_to {FF : Iris.GFunctors} : cif.{u} FF → cif.{max u w} FF
    | cif.cifs_all (A : Type u) Φ =>
        cif.cifs_all (ULift.{w, u} A) (λ a => lift_cif_to (Φ a.down))
    | cif.cifs_ex A Φ =>
        cif.cifs_ex (ULift.{w, u} A) (λ a => lift_cif_to (Φ a.down))
    | cif.cifs_bin s P Q => cif.cifs_bin s (lift_cif_to P) (lift_cif_to Q)
    | cif.cifs_un s P    => cif.cifs_un s (lift_cif_to P)
    | cif.cifs_pure P    => cif.cifs_pure P
    | cif.cifs_later iP  => cif.cifs_later iP
    | cif.cifs_inv N P   => cif.cifs_inv N (lift_cif_to P)
    | @cif.cifs_own _ A _ inst a => @cif.cifs_own _ A _ inst a
end

def cifs_wandiff {FF} (P Q : cif FF) : cif FF :=
  cif.cifs_bin cif_binsel.cifs_and
    (cif.cifs_bin cif_binsel.cifs_wand P Q)
    (cif.cifs_bin cif_binsel.cifs_wand Q P)


def cif_inv {FF} (N : Namespace) (F : cif.{u} FF) : cif.{u + 1} FF :=
  -- ∃ Q,
  cif.cifs_ex.{u + 1} (cif.{u} FF) fun Q =>
    cif.cifs_bin.{u + 1} cif_binsel.cifs_sep
      -- Q ∗-∗ F
      ((cifs_wandiff (lift_cif_to.{u, u + 1} Q) (lift_cif_to.{u, u + 1}  F)))
      -- inv N Q
      (cif.cifs_inv.{u + 1} N (lift_cif_to.{u, u + 1} Q))
