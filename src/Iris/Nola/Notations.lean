import Iris.Nola.Syntax

open Lean

-- define `cif` embedding in `term`
syntax:max "cif(" term ")" : term
syntax:max "term(" term ")" : term

-- allow fallback to `term`
macro_rules
  | `(cif(term($t))) => pure t
  | `(cif($t))       => pure t

-- carry `cif` over some `term` constructs
macro_rules
  | `(cif(($P)))                  => ``((cif($P)))
  | `(cif(if $c then $t else $e)) => ``(if $c then cif($t) else cif($e))
  | `(cif(($P : $t)))             => ``((cif($P) : $t))

macro:max "cif(" P:term " : " t:term ")" : term => `((cif($P) : $t))

/-- Remove an `cif` quotation from a `term` syntax object. -/
partial def unpackCif [Monad m] [MonadRef m] [MonadQuotation m] : Term → m Term
  | `(cif($P))             => do `($P)
  | `($P:ident)              => do `($P)
  | `(?$P:ident)             => do `(?$P)
  | `(($P))                  => do `(($(← unpackCif P)))
  | `($P $[ $Q]*)            => do ``($P $[ $Q]*)
  | `(if $c then $t else $e) => do
    let t ← unpackCif t
    let e ← unpackCif e
    `(if $c then $t else $e)
  | `(($P : $t))             => do ``(($(← unpackCif P) : $t))
  | `($t)                    => `($t:term)

/-- Existential quantification on separation logic propositions. -/
macro "∃" xs:explicitBinders ", " b:term : term => do
  return ⟨← expandExplicitBinders ``cif.cifs_ex xs b⟩

-- `cif` syntax interpretation
macro_rules
  | `(cif(⌜$φ⌝))      => ``(cif.cifs_pure $φ)
  | `(cif($P ∧ $Q))   => ``(cif.cifs_and cif($P) cif($Q))
  | `(cif($P ∨ $Q))   => ``(cif.cifs_or cif($P) cif($Q))
  | `(cif($P → $Q))   => ``(cif.cifs_imp cif($P) cif($Q))
  | `(cif(∃ $xs, $Ψ)) => do expandExplicitBinders ``cif.cifs_ex xs (← ``(cif($Ψ)))
  | `(cif($P ∗ $Q))   => ``(cif.cifs_sep cif($P) cif($Q))
  | `(cif($P -∗ $Q))  => ``(cif.cifs_wand cif($P) cif($Q))
  | `(cif(<pers> $P)) => ``(cif.cifs_pers cif($P))
  | `(cif(▷ $P))      => ``(cif.cifs_later cif($P))

delab_rule cif.cifs_pure
  | `($_ $φ) => ``(cif(⌜$φ⌝))
delab_rule cif.cifs_and
  | `($_ $P $Q) => do ``(cif($(← unpackCif P) ∧ $(← unpackCif Q)))
delab_rule cif.cifs_or
  | `($_ $P $Q) => do ``(cif($(← unpackCif P) ∨ $(← unpackCif Q)))
delab_rule cif.cifs_imp
  | `($_ $P $Q) => do ``(cif($(← unpackCif P) → $(← unpackCif Q)))
delab_rule cif.cifs_all
  | `($_ $_:term fun $x:ident => cif(∀ $y:ident $[$z:ident]*, $Ψ)) => do
    ``(cif(∀ $x:ident $y:ident $[$z:ident]*, $Ψ))
  | `($_ $_:term fun $x:ident => $Ψ) => do ``(cif(∀ $x:ident, $(← unpackCif Ψ)))
delab_rule cif.cifs_ex
  | `($_ $_:term fun $x:ident => cif(∃ $y:ident $[$z:ident]*, $Ψ)) => do
    ``(cif(∃ $x:ident $y:ident $[$z:ident]*, $Ψ))
  | `($_ $_:term fun $x:ident => $Ψ) => do ``(cif(∃ $x:ident, $(← unpackCif Ψ)))
delab_rule cif.cifs_sep
  | `($_ $P $Q) => do ``(cif($(← unpackCif P) ∗ $(← unpackCif Q)))
delab_rule cif.cifs_wand
  | `($_ $P $Q) => do ``(cif($(← unpackCif P) -∗ $(← unpackCif Q)))
delab_rule cif.cifs_pers
  | `($_ $P) => do ``(cif(<pers> $(← unpackCif P)))

delab_rule cif.cifs_pure
  | `($_ True) => ``(cif($(mkIdent `True)))
  | `($_ False) => ``(cif($(mkIdent `False)))
delab_rule cif.cifs_imp
  | `($_ $P cif(False)) => do ``(cif(¬$(← unpackCif P)))
  | `($_ $P $Q) => do ``(cif($(← unpackCif P) -> $(← unpackCif Q)))

/- This is necessary since the `∀` syntax is not defined using `explicitBinders` and we can
therefore not use `expandExplicitBinders` as for `∃`. -/
macro_rules
  | `(cif(∀ _%$tk, $Ψ)) => ``(cif.cifs_all _ (fun _%$tk => cif($Ψ)))
macro_rules
  | `(cif(∀ $x:ident, $Ψ)) => ``(cif.cifs_all _ (fun $x => cif($Ψ)))
macro_rules
  | `(cif(∀ (_%$tk : $t), $Ψ)) => ``(cif.cifs_all $t (fun (_%$tk : $t) => cif($Ψ)))
  | `(cif(∀ (_%$tk $xs* : $t), $Ψ)) =>
    ``(cif.cifs_all $t (fun (_%$tk : $t) => cif(∀ ($xs* : $t), $Ψ)))
macro_rules
  | `(cif(∀ ($x:ident : $t), $Ψ)) => ``(cif.cifs_all $t (fun ($x : $t) => cif($Ψ)))
  | `(cif(∀ ($x:ident $xs* : $t), $Ψ)) =>
    ``(cif.cifs_all $t (fun ($x : $t) => cif(∀ ($xs* : $t), $Ψ)))
macro_rules
  | `(cif(∀ {_%$tk : $t}, $Ψ)) =>
    ``(cif.cifs_all $t (fun {_%$tk : $t}  => cif($Ψ)))
  | `(cif(∀ {_%$tk $xs* : $t}, $Ψ)) =>
    ``(cif.cifs_all $t (fun {_%$tk : $t}  => cif(∀ {$xs* : $t}, $Ψ)))
macro_rules
  | `(cif(∀ {$x:ident : $t}, $Ψ)) =>
    ``(cif.cifs_all $t (fun ($x : $t) => cif($Ψ)))
  | `(cif(∀ {$x:ident $xs* : $t}, $Ψ)) =>
    ``(cif.cifs_all $t (fun ($x : $t) => cif(∀ {$xs* : $t}, $Ψ)))
macro_rules
  | `(cif(∀ $x $y $xs*, $Ψ)) => ``(cif(∀ $x, ∀ $y $xs*, $Ψ))

-- `cif` macros
macro_rules
  | `(cif(True))  => ``(cif.cifs_pure True)
  | `(cif(False)) => ``(cif.cifs_pure False)
  | `(cif(¬$P))   => ``(cif($P → False))

/-- Intuitionistic modality.
```
def intuitionistically (P) := <affine> <pers> P
```
-/

macro_rules
  | `(cif(◇ $P)) => ``(cif.cifs_except0 cif($P))

delab_rule cif.cifs_except0
  | `($_ $P) => do ``(cif(◇ $(← unpackCif P)))

def testCif1 : cif FF :=
  cif.cifs_all Nat (fun x => cif.cifs_all Nat (fun (y : Nat) => cif.cifs_pure (x < y)))

#print testCif1

def testCif2 : cif FF :=
  cif(∀ (x : Nat), ⌜x = 1⌝)

#print testCif2

def testCif3 : cif FF :=
  cif(∀ x (y : Nat), ⌜x < y⌝ -> ⌜¬ x ≥ y⌝)

#print testCif3
