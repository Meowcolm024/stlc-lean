import STLC.Syntax
open Syntax

namespace NbE

/-
Please refer to:
https://homepages.inf.ed.ac.uk/wadler/papers/mpc-2019/system-f-in-agda.pdf
 -/

mutual
  inductive Neutral : Ctx -> Ty -> Type where
  | var : ∀ {Γ A}, (Γ ∋ A) -> Neutral Γ A
  | app : ∀ {Γ A B}, Neutral Γ (A ⇒ B) -> Normal Γ A -> Neutral Γ B

  inductive Normal : Ctx -> Ty -> Type where
  | ne  : ∀ {Γ A}, Neutral Γ A -> Normal Γ A
  | abs : ∀ {Γ A B}, Normal (Γ ,- A) B -> Normal Γ (A ⇒ B)
end

prefix:80 "# " => Neutral.var
infixl:70 " • " => Neutral.app
prefix:60 "ƛ " => Normal.abs

mutual
  def ren_ne {Γ Δ A} (ρ : Ren Γ Δ) (M : Neutral Γ A): Neutral Δ A :=
    match M with
    | # x   => # ρ x
    | M • N => ren_ne ρ M • ren_nf ρ N

  def ren_nf {Γ Δ A} (ρ : Ren Γ Δ) (M : Normal Γ A) : Normal Δ A :=
    match M with
    | .ne M => .ne (ren_ne ρ M)
    | ƛ M   => ƛ ren_nf (ext ρ) M
end

def Sem : Ctx -> Ty -> Type
  | Γ, ⊤     => Normal Γ ⊤
  | Γ, A ⇒ B => Neutral Γ  (A ⇒ B) ⊕ (∀ {Δ}, Ren Γ Δ -> Sem Δ A -> Sem Δ B)

notation:40 Γ " ⊨ " A => Sem Γ A

def reflect {Γ} : {A : Ty} -> (M : Neutral Γ A) -> Γ ⊨ A
  | ⊤, M    => .ne M
  | _ ⇒ _, M => .inl M

def reify {Γ} : {A : Ty} -> (x : Γ ⊨ A) -> Normal Γ A
  | ⊤    , x      => x
  | _ ⇒ _, .inl x => .ne x
  | _ ⇒ _, .inr k => ƛ reify (k .there (reflect (# .here)))

def ren_sem  {Γ Δ} : {A : Ty} -> (ρ : Ren Γ Δ) -> (x : Γ ⊨ A) -> Δ ⊨ A
  | ⊤    , ρ, x      => ren_nf ρ x
  | _ ⇒ _, ρ, .inl x => .inl (ren_ne ρ x)
  | _ ⇒ _, ρ, .inr k => .inr (λ ρ' => k (ρ' ∘ ρ))

abbrev Env (Γ Δ : Ctx) : Type := ∀ {A}, Γ ∋ A -> Δ ⊨ A

def ext_env {Γ Δ Θ A} : (N : Θ ⊨ A) -> (ρ : Ren Δ Θ) -> (η : Env Γ Δ) -> Env (Γ ,- A) Θ
  | N, _, _, _, .here    => N
  | _, ρ, η, _, .there x => ren_sem ρ (η x)

-- strong normalization
def eval {Γ Δ A} (η : Env Γ Δ) (M : Γ ⊢ A) : Δ ⊨ A :=
  match M with
  | # x => η x
  | M • N => match eval η M with
    | .inl x => reflect (x • reify (eval η N))
    | .inr k => k id (eval η N)
  | ƛ M => .inr (λ ρ N => eval (ext_env N ρ η) M)

mutual
  def extr_nf {Γ A} (M : Normal Γ A) : Γ ⊢ A :=
    match M with
    | .ne M => extr_ne M
    | ƛ M   => ƛ extr_nf M

  def extr_ne {Γ A} (M : Neutral Γ A) : Γ ⊢ A :=
    match M with
    | # x   => # x
    | M • N => extr_ne M • extr_nf N
end

def norm {Γ A} (M : Γ ⊢ A) : Γ ⊢ A :=
  extr_nf (reify (eval (λ x => reflect (# x)) M))
