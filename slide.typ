#import "@preview/polylux:0.4.0": *
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set

#set page(paper: "presentation-16-9")
#set page(footer: context [
  #h(1fr)
  #text(size: 16pt)[
    #counter(page).display("1")
  ]
])
#set text(size: 24pt, font: "Helvetica")
#set par(spacing: 1.4em)
#show heading: set block(below: 1.1em)
#show footnote.entry: set text(size: 18pt)
#show list: set par(leading: 1em)
#show raw: set text(size: 20pt, font: "JuliaMono")

#slide[
  #align(horizon + center)[
    = A Tale of Two Calculi

    #strike()[1 April 2026]

    15 April 2026
  ]
]

#slide[
  #align(horizon + center)[
    = It was the Best of #text(fill: blue)[Types]
    = It was the Worst of #text(fill: red)[Runtimes]
  ]
]

#slide[
  = PL Research can be Painful...

  - Start with pen and paper rules;
  - Formalize the calculus using some proof assistants; // (#emoji.chicken.male);
  - *Reimplement* everything in some functional languages; // (#emoji.camel);
  - Can we just use *one* set of codes for everything? 
  - Interestingly, we have: // (#emoji.curry):
    - _Proposition as Types_
    - _Proofs as Programs_
]

#slide[
  #align(center + horizon)[
    = Mechanization as Implementation
  ]
]

#slide[
  = The Surface Syntax

  The plain, old, and boring types and terms AST found in every prototype written in Haskell...

  ```lean
  inductive Ty : Type
  | base : Ty           -- T      (base type)
  | arr  : Ty → Ty → Ty -- A => B (arrow type)

  inductive Raw : Type
  | var : String → Raw            -- x          (variable)
  | app : Raw → Raw → Raw         -- s t        (application)
  | abs : String → Ty → Raw → Raw -- \(x: A). t (lambda)
  ```
]

#slide[
  = The Parser

  Parsing have never been so easy (*partially*) by importing `Parsec`!

  ```lean
  import Std.Internal.Parsec.String
  ```

  With `Parsec`, can write parsers just like in Haskell...

  ```lean
  partial def parseTy : Parser Ty   -- details skipped
  partial def parseRaw : Parser Raw -- details skipped
  ```

  If you appreciate totality, you might need to check out the *total parser* (_agdarsec_).

]

#slide[
  = The Raw Syntax is NOT Enough

  Being a *modern* PL researcher, the named and untyped raw syntax
  can feel way too ... *pedestrian*. 
  
  To truly feel the rigor, we demand more:

  - *Well-Typed Terms:* You really prefer JavaScript and Python?
  - *De Bruijn Indices:* Who doesn't enjoy spending hours figuring out variables whose names vary depending on the number of $lambda$s?

]

#slide[
  = Variables are Lookups

  #text(fill: blue)[*Contexts*], just a fancy list of types...

  ```lean
  inductive Ctx : Type
  | nil  : Ctx             -- ∅      (empty context)
  | cons : Ctx → Ty → Ctx  -- Γ ,- A (ctx extension)
  ```

  #text(fill: blue)[*Lookups*], just list indexing...

  ```lean
  inductive Lookup : Ctx → Ty → Type -- Γ ∋ A
  | here  : ∀ {Γ A}, Lookup (Γ ,- A) A
  | there : ∀ {Γ A B}, Lookup Γ A → Lookup (Γ ,- B) A
  ```

]

#slide[
  = Terms Again, now Typed ... _Intrinsically_

  #text(fill: blue)[*Terms*] again, now shipped with #text(fill: blue)[*de bruijn index*] and #text(fill: blue)[*types*]!

  ```lean
  inductive Tm : Ctx → Ty → Type
  | var : ∀ {Γ A}, Γ ∋ A → Tm Γ A
  | app : ∀ {Γ A B}, Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  | abs : ∀ {Γ A B}, Tm (Γ ,- A) B → Tm Γ (A ⇒ B)

  notation:40 Γ " ⊢ " A => Tm Γ A -- Γ ⊢ A
  prefix:80 "# " => Tm.var        -- # x
  infixl:70 " • " => Tm.app       -- M • N
  prefix:60 "ƛ " => Tm.abs        -- ƛ M
  ```

]

#slide[
  = Now, What?

  - We have the plain old #text(fill: green)[raw syntax] ...
  - We have our great #text(fill: blue)[intrinsically typed terms] ...
  - We need to bridge them via a #text(fill: red)[fancy process] ...
]

#slide[
  = Type Inference!

  In case you have forgotten how to type check STLC. Here are the rules:

  #align(center, rule-set(
    prooftree(
      rule(
        name: "(T-Var)",
        $(x: tau) in Gamma$,
        $Gamma tack.r x : tau$,
      ),
    ),
    prooftree(
      rule(
        name: "(T-App)",
        $Gamma tack.r s : tau -> sigma$,
        $Gamma tack.r t : tau$,
        $Gamma tack.r s thin t : sigma$,
      ),
    ),
    prooftree(
      rule(
        name: "(T-Abs)",
        $Gamma, x: tau tack.r t : sigma$,
        $Gamma tack.r lambda x. thin t : tau -> sigma$,
      ),
    ),
  ))
]

#slide[
  = Setting up the Stage: _Monads_

  The #text(fill: blue)[*type checking monad*], since there are always type errors in our programs.

  ```lean
  abbrev TC (A : Type) : Type := Except String A

  def typeError {A} (msg : String) : TC A := .error msg
  ```
]

#slide[
  = Setting up the Stage: _Environments_

  The #text(fill: blue)[*typing environment*], just a boring mapping between the names and types.

  ```lean
  abbrev Env : Type := List (String × Ty)
  ```

  And we can map `Env` to `Ctx` by dropping the names.

  ```lean
  def conv : (ctx : Env) -> Ctx
  | []             => ∅
  | (_, A) :: ctx' => conv ctx' ,- A
  ```
]

#slide[
  = The Type ... _exists_ ... in the Context

  `WellScoped`, a fancy structure of the plain old existential:
  $exists tau, Gamma in.rev tau$.

  ```lean
  structure WellScoped (ctx : Env) : Type where
    mk ::
    ty : Ty
    ix : conv ctx ∋ ty
  ```

  If a variable is well scoped, it must have a corresponding index under the context.
]

#slide[
  = From Names to Lookups

  Well, it is just a `elemIndex` function...

  ```lean
  def lookup (ctx : Env) (x : String) : TC (WellScoped ctx) :=
    match ctx with
    | []              => typeError s!"Unbounded variable: {x}"
    | (x', A) :: ctx' =>
      if x' == x
        then return WellScoped.mk A .here
        else do
          let WellScoped.mk A ix <- lookup ctx' x
          return WellScoped.mk A (.there ix)
  ```
]

#slide[
  = The not so Rigorous Well Typed Terms

  `WellTyped`, another fancy structure of $exists tau, Gamma tack.r tau$.

  ```lean
  structure WellTyped (ctx : Env) : Type where
    mk ::
    ty : Ty
    tm : conv ctx ⊢ ty
  ```

  But it is not so rigorous, as we won't know whether `tm` is truly the same
  as the original raw term, unless we add a proof that show equality of terms after _type erasure_...

]

#slide[
  #show raw: set text(size: 17pt)
  = Inference!

  #place(dy: 25pt)[
    ```lean
    def infer (ctx : Env) (term : Raw) : TC (WellTyped ctx) :=
      match term with
      | .var x => do let WellScoped.mk A ix <- lookup ctx x
                     return WellTyped.mk A (# ix)
      | .app s t => do
        let WellTyped.mk TAB M <- infer ctx s
        let WellTyped.mk TA N <- infer ctx t
        match TAB with
        | A ⇒ B => match decEq A TA with
          | .isTrue rfl => return WellTyped.mk B (M • N)
          | .isFalse _  => typeError s!"Expect type {A} but got {TA}"
        | _ => typeError s!"Not a function type: {TAB}"
      | .abs x A t => do let WellTyped.mk B M <- infer ((x, A) :: ctx) t
                         return WellTyped.mk (A ⇒ B) (ƛ M)
    ```
  ]
]

#slide[
  = Towards Metathoery

  #text(fill: blue)[*Value*], nothing more than a lambda.

  ```lean
  inductive Value : ∀ {Γ A}, (Γ ⊢ A) -> Type
  | abs : ∀ {Γ A B}, (M : Γ ,- A ⊢ B) -> Value (ƛ M)
  ```

  #text(fill: blue)[*Parallel substitutions*], now proudly typed ...

  ```lean
  -- renamings
  abbrev Ren (Γ Δ : Ctx) : Type := ∀ {A}, Γ ∋ A -> Δ ∋ A
  -- substitutions
  abbrev Sub (Γ Δ : Ctx) : Type := ∀ {A}, Γ ∋ A -> Δ ⊢ A
  ```
]

#slide[
  = Renamings

  ```lean
  def ext {Γ Δ} (ρ : Ren Γ Δ) : ∀ {A}, Ren (Γ ,- A) (Δ ,- A)
    | _, _, .here    => .here
    | _, _, .there x => .there (ρ x)

  def ren {Γ Δ A} (ρ : Ren Γ Δ) (M : Γ ⊢ A) : Δ ⊢ A :=
    match M with
    | # x   => # ρ x
    | M • N => ren ρ M • ren ρ N
    | ƛ M   => ƛ ren (ext ρ) M
  ```
]

#slide[
  = Substitutions

  ```lean
  def exts {Γ Δ} (σ : Sub Γ Δ) : ∀ {A}, Sub (Γ ,- A) (Δ ,- A)
    | _, _, .here    => # .here
    | _, _, .there x => ren .there (σ x)

  def sub {Γ Δ A} (σ : Sub Γ Δ) (M : Γ ⊢ A) : Δ ⊢ A :=
    match M with
    | # x   => σ x
    | M • N => sub σ M • sub σ N
    | ƛ M   => ƛ sub (exts σ) M
  ```
]

#slide[
  = Finally, Single Substitution

  ```lean
  def cons {Γ Δ A} (M : Δ ⊢ A) (σ : Sub Γ Δ) : Sub (Γ ,- A) Δ
    | _, .here    => M
    | _, .there x => σ x
  
  def ids {Γ} : Sub Γ Γ := λ x => # x

  def sub_zero {Γ A} (M : Γ ⊢ A) : Sub (Γ ,- A) Γ := 
    cons M ids

  notation M "[" N "]" => sub (sub_zero N) M
  ```

  // - Definitions of parallel renaming and substitution here are not really different from the _intrinsically-scoped_ or the _unscoped_ ones.
  // - However, a second order system would be more complicated.
]

#slide[
  = The Good Old Small-step Semantics

  The classical #text(fill: blue)[*small-step*] operational semantic of weak reduction.

  ```lean
  inductive Step : ∀ {Γ A}, (Γ ⊢ A) -> (Γ ⊢ A) -> Type
  | app_l : ∀ {Γ A B} {M M' : Γ ⊢ A ⇒ B} {N : Γ ⊢ A},
    Step M M' -> Step (M • N) (M' • N)
  | app_r : ∀ {Γ A B} {M : Γ ,- A ⊢ B} {N N' : Γ ⊢ A},
    Step N N' -> Step ((ƛ M) • N) ((ƛ M) • N')
  | beta  : ∀ {Γ A B} {M : Γ ,- A ⊢ B} {N : Γ ⊢ A},
    Value N → Step ((ƛ M) • N) (M [ N ])

  notation M " —→ " N => Step M N
  ```
]

#slide[
  = To _Step_ or not to _Step_, that is the _Progress_

  - A well typed term is either a *value* or it takes a *step*.

  ```lean
  inductive Progress {Γ A} (M : Γ ⊢ A) : Type
  | done : Value M -> Progress M
  | step : ∀ {N : Γ ⊢ A}, (M —→ N) -> Progress M
  ```

  - What about *preservation*? It is already embedded in the small-step semantic!
  - Why not `Prop`? We really need that extra "computational power" from `Type` (later).
]

#slide[
  = Now, Real Progress

  Just a recursive function, what's the problem?

  ```lean
  def progress {A} (M : ∅ ⊢ A) : Progress M :=
    match M with
    | M • N => match progress M, progress N with
      | .done VM, .done VN  =>
        match VM with | .abs M' => .step (.beta VN)
      | .done VM, .step stN =>
        match VM with | .abs M' => .step (.app_r stN)
      | .step stM, _ => .step (.app_l stM)
    | ƛ M => .done (.abs M)
  ```

]

#slide[
  = Step, Step, Step, ..., Done

  The familiar multi-step reduction, now indexed by _contexts_ and _types_.

  ```lean
  inductive Multi : ∀ {Γ A}, (Γ ⊢ A) -> (Γ ⊢ A) -> Type
  | done : ∀ {Γ A} (M : Γ ⊢ A), Multi M M
  | step : ∀ {Γ A} (L : Γ ⊢ A) {M N},
    (L —→ M) -> Multi M N -> Multi L N

  notation M " —→* " N => Multi M N
  ```
]

#slide[
  #show raw: set text(size: 18pt)
  = Evaluation (Gas Included)

  Just keep progressing ... until we've #text(fill: red)[run out of gas]!

  #place(dy: 25pt)[
    ```lean
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
    ```
  ]
]

#slide[
  = Wait! Why do we need gas?

  - *STLC* is #text(fill: red)[always terminating!] A term can always reduce to a value.
  - Why don't we just remove the gas? It only requires #text(fill: blue)[a tiny bit of] extra work.

  ```lean
  structure Halts {A} (M : ∅ ⊢ A) : Type where
    mk ::
    N     : ∅ ⊢ A
    trace : M —→* N
    value : Value N
  ```
]

#slide[
  = Logical Relation

  - The logical predicate for normalizing terms:

  ```lean
  def Norm {A} (M : ∅ ⊢ A) : Type :=
    match A with
    | ⊤     => Halts M
    | _ ⇒ _ => Halts M × (∀ {N}, Norm N → Norm (M • N))
  ```

  - The "good" substitution w.r.t. to the context $Gamma$:

  ```lean
  abbrev Close {Γ} (σ : Sub Γ ∅) : Type := 
    ∀ {A}, (x : Γ ∋ A) → Norm (σ x)
  ```
]

#slide[
  #show raw: set text(size: 18pt)
  = Way too many Lemmas and Definitions ...

  ```lean
  def multi_trans {Γ A} {L M N : Γ ⊢ A} : (L —→* M) → (M —→* N) → (L —→* N)
  def app_r_cong {Γ A B} {M : Γ ,- A ⊢ B} {N N' : Γ ⊢ A} : (N —→* N') → ((ƛ M) • N) —→* ((ƛ M) • N')
  def step_halts {A} {M N : ∅ ⊢ A} (st : M —→ N) : Halts M → Halts N
  def step_halts_rev {A} {M N : ∅ ⊢ A} (st : M —→ N) : Halts N → Halts M
  def step_norm : ∀ {A} {M N : ∅ ⊢ A}, (M —→ N) → Norm M → Norm N
  def step_norm_rev : ∀ {A} {M N : ∅ ⊢ A}, (M —→ N) → Norm N → Norm M
  def multi_norm {A} {M N : ∅ ⊢ A} : (M —→* N) → Norm M → Norm N
  def multi_norm_rev {A} {M N : ∅ ⊢ A} : (M —→* N) → Norm N → Norm M
  -- all details skipped!
  ```
]

#slide[
  = Skipping the Boring Parts

  - *Skipping* #text(fill: red)[*computational irrelevant*] parts (`Prop`) does not affect evaluation (if your axioms are reasonable).
  - For example, the tedious _substitution lemmas_ can be skipped during rapid development.

  ```lean
  axiom sub_id {Γ A} : ∀ (M : Γ ⊢ A), sub ids M = M
  axiom sub_ext_sub {Γ Δ} {σ : Sub Γ Δ} : 
    ∀ {A B} (M : Γ ,- B ⊢ A) (N : Δ ⊢ B), 
    sub (cons N σ) M = (sub (exts σ) M) [ N ]
  ```
]

#slide[
  = Normalizing Term Halts

  - Well, it is already encoded in the logical predicate...

  ```lean
  def norm_halts {A} {M : ∅ ⊢ A} (nm : Norm M) : Halts M :=
    match A with
    | ⊤     => nm
    | _ ⇒ _ => nm.fst
  ```
]

#slide[
  #show raw: set text(size: 19pt)
  = Well-Typed Terms are Normalizing

  - The classical normalization proof, now also intrinsically typed.
  - The cases for variable and application are mostly trivial.

  ```lean
  def norm {Γ A σ} (M : Γ ⊢ A) (G : Close σ) : Norm (sub σ M) :=
    match M with
    | # x   => G x
    | M • N => (norm M G).snd (norm N G)
    | ƛ M   => -- next page
  ```
]

#slide[
  #show raw: set text(size: 19pt)

  - The case for function needs a bit more work.

  ```lean
  | ƛ M =>
    let k : ∀ {N}, Norm N → Norm (sub σ (ƛ M) • N) := λ nn =>
      let (.mk N' mt' v') := norm_halts nn
      let lem1 := by
        rw [sub_ext_sub M N']
        exact multi_trans (app_r_cong mt') 
          (.step _ (.beta v') (.done _))
      let lem2 := norm (σ := cons N' σ) M
        (λ | .here => multi_norm mt' nn | .there x => G x)
      multi_norm_rev lem1 lem2
    (Halts.mk _ (.done _) (.abs _) , k)
  ```
]

#slide[
  = Finally, Evaluation without Gas!

  - Combining the two lemmas above, we can now reduce a term to value without gas!

  ```lean
  def halts {A} (M : ∅ ⊢ A) : Halts M := by
    let nm := norm (σ := ids) M (λ _ => by contradiction)
    rw [<- sub_id M]
    exact norm_halts nm
  ```
]

#slide[
  = Normalization by Evaluation (NbE)

  Unfortunately, the current evaluation function (`halts`) is way too #text(fill: blue)[*weak*] and #text(fill: red)[*slow*]:

  - We do not *under lambdas* (why not?).
  - Taking *one step* at a time is too slow.
  - STLC has functions $lambda x. t$, and Lean also has functions, `λ x => t`, what a *coincidence*! Can we take advantage of that?
  - *NbE*: Embedding our STLC terms into Lean terms.
]

#slide[
  #show raw: set text(size: 18pt)
  = _Neutrals_, _Normals_, defined mutually

  *Values*, but much fancier.

  ```lean
  mutual
    inductive Neutral : Ctx -> Ty -> Type
    | var : ∀ {Γ A}, (Γ ∋ A) -> Neutral Γ A -- # x
    | app : ∀ {Γ A B}, -- M • N
      Neutral Γ (A ⇒ B) -> Normal Γ A -> Neutral Γ B
    inductive Normal : Ctx -> Ty -> Type
    | ne  : ∀ {Γ A}, Neutral Γ A -> Normal Γ A
    | abs : ∀ {Γ A B}, -- ƛ M
      Normal (Γ ,- A) B -> Normal Γ (A ⇒ B)
  end
  ```
]

#slide[
  = Semantic Typing

  - A semantic function is either a _neutral term_, or a_ meta-level (Lean) function_ (with an extra argument for renaming).

  ```lean
  def Sem : Ctx -> Ty -> Type
    | Γ, ⊤     => Normal Γ ⊤
    | Γ, A ⇒ B => Neutral Γ (A ⇒ B) ⊕
      (∀ {Δ}, Ren Γ Δ -> Sem Δ A -> Sem Δ B)

  notation:40 Γ " ⊨ " A => Sem Γ A
  ```

   - `Sem` is well-defined, as it is structurally decreasing (on `Ty`).
]

#slide[
  = Just Three More Renamings ...

  We need a few more boring renaming functions.

  ```lean
  mutual
    def ren_ne {Γ Δ A} (ρ : Ren Γ Δ) (M : Neutral Γ A)
      : Neutral Δ A -- skipped
    def ren_nf {Γ Δ A} (ρ : Ren Γ Δ) (M : Normal Γ A)
      : Normal Δ A -- skipped
  end

  def ren_sem  {Γ Δ} (ρ : Ren Γ Δ)
    : ∀ {A}, (x : Γ ⊨ A) -> Δ ⊨ A -- skipped
  ```
]

#slide[
  = Reflection and Reification

  - *Reflection* embeds a neutral term into a semantic value.
  - *Reification* converts a semantic value into a term in normal form.

  ```lean
  def reflect {Γ} : ∀ {A}, (M : Neutral Γ A) -> Γ ⊨ A
    | ⊤    , M => .ne M
    | _ ⇒ _, M => .inl M

  def reify {Γ} : ∀ {A}, (x : Γ ⊨ A) -> Normal Γ A
    | ⊤    , x      => x
    | _ ⇒ _, .inl x => .ne x
    | _ ⇒ _, .inr k => ƛ reify (k .there (reflect (# .here)))
  ```
]

#slide[
  = Environment

  - An *environment* is a function from lookup to semantic value.
  - `exte` extends the environment with semantic value `N`.

  ```lean
  abbrev Env (Γ Δ : Ctx) : Type := ∀ {A}, Γ ∋ A -> Δ ⊨ A

  def exte {Γ Δ A} (N : Δ ⊨ A) (η : Env Γ Δ) : Env (Γ ,- A) Δ
  | _, .here    => N
  | _, .there x => η x
  ```
]

#slide[
  = Evaluation, Finally ...

  *Evaluation*, just a big-step style evaluator made complicated.

  ```lean
  def eval {Γ Δ A} (η : Env Γ Δ) (M : Γ ⊢ A) : Δ ⊨ A :=
    match M with
    | # x => η x
    | M • N => match eval η M with
      | .inl x => reflect (x • reify (eval η N))
      | .inr k => k id (eval η N)
    | ƛ M => .inr (λ ρ N => eval (exte N (ren_sem ρ ∘ η)) M)
  ```

  Is the result really in normal form? Proof is left as an exercise.
]

#slide[
  = Back to the Terms

  Finally we can convert the neutral and normal terms back to our standard intrinsically typed terms.

  ```lean
  mutual
    def extr_nf {Γ A} (M : Normal Γ A) : Γ ⊢ A  -- skipped
    def extr_ne {Γ A} (M : Neutral Γ A) : Γ ⊢ A -- skipped
  end

  def norm {Γ A} (M : Γ ⊢ A) : Γ ⊢ A :=
    extr_nf (reify (eval (λ x => reflect (# x)) M))
  ```
]

#slide[
  #show raw: set text(size: 18pt)
  = Read, Evaluate, Print, ... _Loop_!

  ```txt
  > (\(x: T => T). x) (\(x: T). (\(y: T). y) x)
  ----------------------------------------
  Weak Reduction:
    ((λ. x0) (λ. ((λ. x0) x0))) —→* (λ. ((λ. x0) x0))
  Reduction Trace:
    —→ ((λ. x0) (λ. ((λ. x0) x0)))
    —→ (λ. ((λ. x0) x0))
    ∎
  ----------------------------------------
  Strong Normalization (NbE):
    ((λ. x0) (λ. ((λ. x0) x0))) ⇓ (λ. x0)
  ----------------------------------------
  ```
]

#slide[
  = Parse Errors, Name Errors, Type Errors...

  ```txt
  > \x.x
  [Parse Error] offset 1: expected: (
  > (\(x: T). x) y
  [Type Error] Unbounded variable: y
  > \(x: T). x x
  [Type Error] Not a function type: ⊤
  >
  ```
]

#slide[
  = Key Takeaways

  - *Lean 4* has a (mostly) working dependent pattern matching.
  - The *mechanization* can indeed be the *prototype*.
  - We can even take a step further (but way too far):
    - Have the _paper_, the _mechanization_, and _prototype_, all in a *Literate Agda* script.
  - *Typst* has an OK-ish highlighting for Lean.

]
