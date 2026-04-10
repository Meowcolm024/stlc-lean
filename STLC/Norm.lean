import STLC.Syntax
import STLC.Semantic

open Syntax Semantic

namespace Norm

structure Halts {A} (M : ∅ ⊢ A) : Type where
  mk ::
  N     : ∅ ⊢ A
  trace : M —→* N
  value : Value N

deriving instance Repr for Halts

-- the logical predicate
def Norm {A} (M : ∅ ⊢ A) : Type :=
  match A with
  | ⊤     => Halts M
  | _ ⇒ _ => Halts M × (∀ {N}, Norm N → Norm (M • N))

-- "good" substitution
abbrev Close {Γ} (σ : Sub Γ ∅) : Type := ∀ {A}, (x : Γ ∋ A) → Norm (σ x)

def step_halts {A} {M N : ∅ ⊢ A} (st : M —→ N) : Halts M → Halts N
  | .mk _ mt v => match mt with
    | .done _         => Empty.elim (value_no_step v st)
    | .step _ st' mt' => by
      rw [step_determ st st']
      exact .mk _ mt' v

def step_halts_rev {A} {M N : ∅ ⊢ A} (st : M —→ N) : Halts N → Halts M
  | .mk N' mt v => match mt with
    | .done _         => .mk _ (.step _ st (.done _)) v
    | .step _ st' mt' => .mk _ (.step _ st (.step _ st' mt')) v

def step_norm : ∀ {A} {M N : ∅ ⊢ A}, (M —→ N) → Norm M → Norm N
  | ⊤    , _, _, st, nm      => step_halts st nm
  | _ ⇒ _, _, _, st, (nm, k) => (step_halts st nm, λ nn => step_norm (.app_l st) (k nn))

def step_norm_rev : ∀ {A} {M N : ∅ ⊢ A}, (M —→ N) → Norm N → Norm M
  | ⊤    , _, _, st, nm      => step_halts_rev st nm
  | _ ⇒ _, _, _, st, (nm, k) => (step_halts_rev st nm, λ nn => step_norm_rev (.app_l st) (k nn))

def multi_norm {A} {M N : ∅ ⊢ A} : (M —→* N) → Norm M → Norm N
  | .done _      , nm => nm
  | .step _ st mt, nm => multi_norm mt (step_norm st nm)

def multi_norm_rev {A} {M N : ∅ ⊢ A} : (M —→* N) → Norm N → Norm M
  | .done _      , nm => nm
  | .step _ st mt, nm => step_norm_rev st (multi_norm_rev mt nm)

-- boring substitution lemmas, see https://plfa.github.io/Substitution/
axiom sub_id {Γ A} : ∀ (M : Γ ⊢ A), sub ids M = M
axiom sub_ext_sub {Γ Δ} {σ : Sub Γ Δ} :
  ∀ {A B} (M : Γ ,- B ⊢ A) (N : Δ ⊢ B),
  sub (cons N σ) M = (sub (exts σ) M) [ N ]

def norm_halts {A} {M : ∅ ⊢ A} (nm : Norm M) : Halts M :=
  match A with
  | ⊤     => nm
  | _ ⇒ _ => nm.fst

def norm {Γ A σ} (M : Γ ⊢ A) (G : Close σ) : Norm (sub σ M) :=
  match M with
  | # x   => G x
  | M • N => (norm M G).snd (norm N G)
  | ƛ M   =>
    let k : ∀ {N}, Norm N → Norm (sub σ (ƛ M) • N) := λ nn =>
      let (.mk N' mt' v') := norm_halts nn
      let lem1 := by
        rw [sub_ext_sub M N']
        exact multi_trans (app_r_cong mt') (.step _ (.beta v') (.done _))
      let lem2 := norm (σ := cons N' σ) M
        (λ | .here => multi_norm mt' nn | .there x => G x)
      multi_norm_rev lem1 lem2
    (Halts.mk _ (.done _) (.abs _) , k)

def halts {A} (M : ∅ ⊢ A) : Halts M := by
  let nm := norm (σ := ids) M (λ _ => by contradiction)
  rw [<- sub_id M]
  exact norm_halts nm
