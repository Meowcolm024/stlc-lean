import STLC.Syntax
open Syntax

namespace TypeCheck

/-
Please refer to:
https://agda.readthedocs.io/en/stable/language/syntactic-sugar.html
 -/

abbrev TC (A : Type) : Type := Except String A

def typeError {A} (msg : String) : TC A := .error msg

abbrev Context : Type := List (String × Ty)

def conv : (ctx : Context) -> Ctx
  | [] => ∅
  | (_, A) :: ctx' => conv ctx' ,- A

structure WellScoped (ctx : Context) : Type where
  mk ::
  ty : Ty
  ix : conv ctx ∋ ty

deriving instance Repr for WellScoped

def lookup (ctx : Context) (x : String) : TC (WellScoped ctx) :=
  match ctx with
  | []              => typeError s!"unbounded variable {x}"
  | (x', A) :: ctx' =>
    if x' == x
      then return WellScoped.mk A .here
      else do
        let WellScoped.mk A ix <- lookup ctx' x
        return WellScoped.mk A (.there ix)

/-
WellTyped is actually not strong enough as we didn't
prove that the elaborated term is the same as the raw term.
This requires an erasure process, but also need to restore
the names, which can be challenging (sort of).
 -/
structure WellTyped (ctx : Context) : Type where
  mk ::
  ty : Ty
  tm : conv ctx ⊢ ty

deriving instance Repr for WellTyped

def infer (ctx : Context) (raw : Raw) : TC (WellTyped ctx) :=
  match raw with
  | .var x => do
    let WellScoped.mk A ix <- lookup ctx x
    return WellTyped.mk A (# ix)
  | .app s t => do
    let WellTyped.mk TAB M <- infer ctx s
    let WellTyped.mk TA N <- infer ctx t
    match TAB with
    | A ⇒ B => match decEq A TA with
      | .isTrue rfl => return WellTyped.mk B (M • N)
      | .isFalse _ => typeError "application type mismatch"
    | _ => typeError "trying to apply a non function type"
  | .abs x A t => do
    let WellTyped.mk B M <- infer ((x, A) :: ctx) t
    return WellTyped.mk (A ⇒ B) (ƛ M)
