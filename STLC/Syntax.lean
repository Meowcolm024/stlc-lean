namespace Syntax

inductive Ty : Type where
| base : Ty
| arr : Ty → Ty → Ty

notation "⊤" => Ty.base
infixr:70 " ⇒ " => Ty.arr

deriving instance Repr, Inhabited, DecidableEq for Ty

inductive Ctx : Type where
| nil : Ctx
| cons : Ctx → Ty → Ctx

notation "∅" => Ctx.nil
infixl:65 " ,- " => Ctx.cons

deriving instance Repr, DecidableEq for Ctx

inductive Lookup : Ctx → Ty → Type where
| here : ∀ {Γ A}, Lookup (Γ ,- A) A
| there : ∀ {Γ A B}, Lookup Γ A → Lookup (Γ ,- B) A

infix:50 " ∋ " => Lookup

deriving instance Repr, DecidableEq for Lookup

inductive Tm : Ctx → Ty → Type where
| var : ∀ {Γ A}, Γ ∋ A → Tm Γ A
| app : ∀ {Γ A B}, Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
| abs : ∀ {Γ A B}, Tm (Γ ,- A) B → Tm Γ (A ⇒ B)

notation:40 Γ " ⊢ " A => Tm Γ A

prefix:80 "# " => Tm.var
infixl:70 " • " => Tm.app
prefix:60 "ƛ " => Tm.abs

deriving instance Repr, DecidableEq for Tm

abbrev Ren (Γ Δ : Ctx) : Type := ∀ {A}, Γ ∋ A -> Δ ∋ A
abbrev Sub (Γ Δ : Ctx) : Type := ∀ {A}, Γ ∋ A -> Δ ⊢ A

def ext {Γ Δ} (ρ : Ren Γ Δ) : ∀ {A}, Ren (Γ ,- A) (Δ ,- A)
  | _, _, .here => .here
  | _, _, .there x => .there (ρ x)

def ren {Γ Δ A} (ρ : Ren Γ Δ) (M : Γ ⊢ A) : Δ ⊢ A :=
  match M with
  | # x => # ρ x
  | M • N => ren ρ M • ren ρ N
  | ƛ M => ƛ ren (ext ρ) M

def exts {Γ Δ} (σ : Sub Γ Δ) : ∀ {A}, Sub (Γ ,- A) (Δ ,- A)
  | _, _, .here => # .here
  | _, _, .there x => ren .there (σ x)

def sub {Γ Δ A} (σ : Sub Γ Δ) (M : Γ ⊢ A) : Δ ⊢ A :=
  match M with
  | # x => σ x
  | M • N => sub σ M • sub σ N
  | ƛ M => ƛ sub (exts σ) M

def sub_zero {Γ A} (M : Γ ⊢ A) : Sub (Γ ,- A) Γ
  | _, .here => M
  | _, .there x => # x

notation M "[" N "]" => sub (sub_zero N) M

inductive Raw : Type where
| var : String → Raw
| app : Raw → Raw → Raw
| abs : String → Ty → Raw → Raw

deriving instance Repr, Inhabited, DecidableEq for Raw

private def Ty.pretty : Ty -> String
  | ⊤ => "⊤"
  | ⊤ ⇒ B => s!"⊤ -> {Ty.pretty B}"
  | A ⇒ B => s!"({Ty.pretty A}) -> {Ty.pretty B}"

instance : ToString Ty where
  toString t := Ty.pretty t

private def Lookup.pretty : {Γ : Ctx} -> {A : Ty} -> Lookup Γ A -> Nat
  | _, _, .here => 0
  | _, _, .there i => Lookup.pretty i + 1

instance {Γ A} : ToString (Lookup Γ A) where
  toString i := s!"{Lookup.pretty i}"

private def Tm.pretty : {Γ : Ctx} -> {A : Ty} -> Tm Γ A -> String
  | _, _, .var i => s!"x{i}"
  | _, _, .app f a => s!"({f.pretty} {a.pretty})"
  | _, _, .abs b => s!"(λ. {b.pretty})"

instance {Γ A} : ToString (Γ ⊢ A) where
  toString t := t.pretty

private def Raw.pretty : Raw -> String
  | .var s => s
  | .app f a => s!"({f.pretty} {a.pretty})"
  | .abs s ty b => s!"(λ({s} : {repr ty}). {b.pretty})"

instance : ToString Raw where
  toString r := r.pretty
