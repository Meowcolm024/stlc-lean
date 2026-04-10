import STLC.Syntax
open Syntax

namespace Semantic

/-
Please refer to
https://plfa.github.io/DeBruijn/
 -/

inductive Value : ∀ {Γ A}, (Γ ⊢ A) -> Type where
| abs : ∀ {Γ A B}, (M : Γ ,- A ⊢ B) -> Value (ƛ M)

deriving instance Repr for Value

-- weak small step
inductive Step : ∀ {Γ A}, (Γ ⊢ A) -> (Γ ⊢ A) -> Type where
| app_l : ∀ {Γ A B} {M M' : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}, Step M M' -> Step (M • N) (M' • N)
| app_r : ∀ {Γ A B} {M : Γ ,- A ⊢ B} {N N' : Γ ⊢ A}, Step N N' -> Step ((ƛ M) • N) ((ƛ M) • N')
| beta  : ∀ {Γ A B} {M : Γ ,- A ⊢ B} {N : Γ ⊢ A}, Value N → Step ((ƛ M) • N) (M [ N ])

deriving instance Repr for Step

notation M " —→ " N => Step M N

def value_no_step {A} {M : ∅ ⊢ A} : Value M → ∀ {N}, (M —→ N) → Empty
  | .abs _, N, st => by contradiction

def step_determ {A} {M M₁ M₂ : ∅ ⊢ A} : (M —→ M₁) → (M —→ M₂) → M₁ = M₂
  | .app_l st1, .app_l st2 => by rw [step_determ st1 st2]
  | .app_l st1, .app_r st2 => by contradiction
  | .app_l st1, .beta v2   => by contradiction
  | .app_r st1, .app_l st2 => by contradiction
  | .app_r st1, .app_r st2 => by rw [step_determ st1 st2]
  | .app_r st1, .beta v2   => Empty.elim (value_no_step v2 st1)
  | .beta v1  , .app_l st2 => by contradiction
  | .beta v1  , .app_r st2 => Empty.elim (value_no_step v1 st2)
  | .beta v1  , .beta v2   => by rfl

inductive Progress {Γ A} (M : Γ ⊢ A) : Type where
| done : Value M -> Progress M
| step : ∀ {N : Γ ⊢ A}, (M —→ N) -> Progress M

def progress {A} (M : ∅ ⊢ A) : Progress M :=
  match M with
  | M • N => match progress M, progress N with
    | .done VM, .done VN  => match VM with | .abs M' => .step (.beta VN)
    | .done VM, .step stN => match VM with | .abs M' => .step (.app_r stN)
    | .step stM, _        => .step (.app_l stM)
  | ƛ M => .done (.abs M)

inductive Multi : ∀ {Γ A}, (Γ ⊢ A) -> (Γ ⊢ A) -> Type where
| done : ∀ {Γ A} (M : Γ ⊢ A), Multi M M
| step : ∀ {Γ A} (L : Γ ⊢ A) {M N}, (L —→ M) -> Multi M N -> Multi L N

notation M " —→* " N => Multi M N

deriving instance Repr for Multi

def multi_trans {Γ A} {L M N : Γ ⊢ A} : (L —→* M) → (M —→* N) → (L —→* N)
  | .done _        , mt2 => mt2
  | .step _ st1 mt1, mt2 => .step _ st1 (multi_trans mt1 mt2)

def app_r_cong {Γ A B} {M : Γ ,- A ⊢ B} {N N' : Γ ⊢ A} : (N —→* N') → ((ƛ M) • N) —→* ((ƛ M) • N')
  | .done _       => .done _
  | .step _ st mt => .step _ (.app_r st) (app_r_cong mt)

structure Eval {A} (M : ∅ ⊢ A) : Type where
  mk ::
  N     : ∅ ⊢ A
  trace : M —→* N
  fin   : Option (Value N)

def eval {A} : (g : Nat) -> (M : ∅ ⊢ A) -> Eval M
| 0    , M => .mk M (.done M) none
| g + 1, M => match progress M with
  | .done VM          => .mk M (.done M) (some VM)
  | .step (N := N) st => match eval g N with
    | .mk N' trace fin => .mk N' (.step _ st trace) fin

private def Multi.pretty {Γ A} {M N : Γ ⊢ A} (st : M —→* N) : String :=
  match st with
  | .done _       => s!"  —→ {M}\n  ∎"
  | .step L LM MN => s!"  —→ {L}\n{Multi.pretty MN}"

instance {Γ A} {M N : Γ ⊢ A} : ToString (Multi M N) where
  toString s := Multi.pretty s
