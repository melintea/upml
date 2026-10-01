/-
  lake new samekhsm        # scaffold a project
  lake build               # type-check/build everythin

  lean samekhsm.lean
-/
/-
  Lean 4 verification model of Miro Samek's canonical hierarchical state
  machine (HSM), from "Practical UML Statecharts" ch.2 / p.88.

  Extracted from:
    plantuml/hsm/samek-g.plantuml (project `upml`)

  State hierarchy (parent links):

      SuperSuper                      (top / root)
      ├── Super2        initial substate of SuperSuper
      │   └── Super21   initial substate of Super2
      │       └── S211  initial substate of Super21
      └── Super1
          └── S11       initial substate of Super1

  Transition table (event, source, target):

      A : Super21   -> Super21     (self)
      B : Super21   -> S211
      C : Super2    -> Super1
      C : Super1    -> Super2
      D : S211      -> Super21
      D : S11       -> Super1
      D : Super1    -> SuperSuper
      E : SuperSuper-> S11
      F : Super2    -> S11
      F : Super1    -> S211
      G : Super21   -> S11
      G : S11       -> S211
      H : S211      -> SuperSuper
      H : S11       -> SuperSuper

  HSM dispatch semantics modelled here:
    * The machine configuration is a *leaf* state. The set of active states
      is the leaf plus all its ancestors up to the root.
    * On an event, dispatch searches from the current leaf upward through its
      ancestor chain for the first state that declares a handler for that
      event; that transition fires. (Innermost handler wins.)
    * A fired transition src -> tgt executes, in order:
        exit actions from the current leaf up to (not including) the LCA of
        src and tgt, then the transition action, then entry actions from just
        below the LCA down into tgt and on through tgt's initial substates to
        a leaf.
    * The `Super21` precondition guard `(in Super2 && not in Super1)` from the
      chart is modelled and shown to hold whenever Super21 is active.
    * If no active state handles the event, the configuration is unchanged.
-/

namespace SamekHSM

/-- Every named state in the chart. -/
inductive State where
  | SuperSuper
  | Super2
  | Super21
  | S211
  | Super1
  | S11
deriving DecidableEq, Repr

open State

/-- Events A..H. -/
inductive Event where
  | A | B | C | D | E | F | G | H
deriving DecidableEq, Repr

open Event

/-- Parent of a state (`none` for the root). Encodes the hierarchy. -/
def parent : State → Option State
  | SuperSuper => none
  | Super2     => some SuperSuper
  | Super21    => some Super2
  | S211       => some Super21
  | Super1     => some SuperSuper
  | S11        => some Super1

/-- Initial substate (`none` for leaves). Encodes `[*] --> _` arrows. -/
def initialChild : State → Option State
  | SuperSuper => some Super2
  | Super2     => some Super21
  | Super21    => some S211
  | S211       => none
  | Super1     => some S11
  | S11        => none

/-- A state is a leaf iff it has no initial child (no substates). -/
def isLeaf (s : State) : Bool := (initialChild s).isNone

/--
  Complete an entered state down to a leaf by following `initialChild`.
  `fuel` bounds the descent; the hierarchy depth is 4, so 6 is ample.
-/
def completeToLeaf : Nat → State → State
  | 0,       s => s
  | fuel+1,  s =>
    match initialChild s with
    | none       => s
    | some child => completeToLeaf fuel child

/-- The ancestor chain of a state, innermost first (the active-state set). -/
def ancestors : Nat → State → List State
  | 0,     s => [s]
  | n+1,   s =>
    match parent s with
    | none   => [s]
    | some p => s :: ancestors n p

/-- Membership of a state in the active set determined by leaf `leaf`. -/
def active (leaf : State) (s : State) : Bool :=
  (ancestors 6 leaf).contains s

/--
  Local transition relation: the transition declared *on* a given state for a
  given event, if any. This is the raw edge table, keyed by source state.
-/
def localTarget : State → Event → Option State
  -- Super21
  | Super21,    A => some Super21
  | Super21,    B => some S211
  | Super21,    G => some S11
  -- Super2
  | Super2,     C => some Super1
  | Super2,     F => some S11
  -- Super1
  | Super1,     C => some Super2
  | Super1,     D => some SuperSuper
  | Super1,     F => some S211
  -- S211
  | S211,       D => some Super21
  | S211,       H => some SuperSuper
  -- S11
  | S11,        D => some Super1
  | S11,        G => some S211
  | S11,        H => some SuperSuper
  -- SuperSuper
  | SuperSuper, E => some S11
  | _,          _ => none

/-! ## Least common ancestor -/

/-- The ancestor chain including self, outermost-first (root first). -/
def pathFromRoot (s : State) : List State :=
  (ancestors 6 s).reverse

/-- Longest common prefix length of two lists of states. -/
def commonPrefixLen : List State → List State → Nat
  | x :: xs, y :: ys => if x = y then 1 + commonPrefixLen xs ys else 0
  | _,       _       => 0

/-- Last element of a non-empty prefix walk; returns `SuperSuper` as the root
    default (both state paths share the root, so a real LCA is always found). -/
def lastOrRoot : List State → State
  | []      => SuperSuper
  | [x]     => x
  | _ :: xs => lastOrRoot xs

/--
  Least common ancestor of two states. Both share `SuperSuper` as root, so the
  common prefix of their root-first paths is non-empty; the LCA is its last
  element.
-/
def lca (a b : State) : State :=
  let pa := pathFromRoot a
  let pb := pathFromRoot b
  let n  := commonPrefixLen pa pb
  lastOrRoot (pa.take n) -- n ≥ 1 since both paths start at the root

/-! ## Action trace -/

/-- An entry or exit action emitted during a transition. -/
inductive Action where
  | enter (s : State)
  | exit  (s : State)
deriving DecidableEq, Repr

open Action

/-- Exit actions: from leaf `cur` up to, but not including, `stop`. -/
def exitChain : Nat → State → State → List Action
  | 0,     cur, _    => [exit cur]
  | n+1,   cur, stop =>
    if cur = stop then []
    else match parent cur with
         | none   => [exit cur]
         | some p => exit cur :: exitChain n p stop

/-- Root-first list of states strictly below `top` down to and including `tgt`. -/
def enterPath (top tgt : State) : List State :=
  let full := pathFromRoot tgt           -- root ... tgt
  (full.dropWhile (fun s => s != top)).drop 1  -- drop up to & incl. `top`

/-- Entry actions completing through initial substates from `s` to a leaf. -/
def completeEnter : Nat → State → List Action
  | 0,    _ => []
  | n+1,  s => match initialChild s with
               | none       => []
               | some child => enter child :: completeEnter n child

/-- Entry actions entering down to `tgt`, then completing initial substates. -/
def enterChain (top tgt : State) : List Action :=
  (enterPath top tgt).map Action.enter ++ completeEnter 6 tgt

/--
  Fire the transition handled at `src` (source scope) for target `tgt`, from
  the current leaf `curLeaf`. Returns the emitted action trace (exit then
  enter) and the resulting leaf.
-/
def fire (curLeaf src tgt : State) : List Action × State :=
  let anc  := lca src tgt
  let exits := exitChain 6 curLeaf anc
  let enters := enterChain anc tgt
  (exits ++ enters, completeToLeaf 6 tgt)

/--
  Dispatch an event at a leaf configuration: walk up the ancestor chain and
  take the first state that handles `e`, firing it. Returns (trace, new leaf).
  If nothing handles `e`, the leaf is unchanged and the trace is empty.
-/
def dispatchChain : List State → Event → State → (List Action × State)
  | [],      _, cur => ([], cur)
  | s :: ss, e, cur =>
    match localTarget s e with
    | some tgt => fire cur s tgt
    | none     => dispatchChain ss e cur

/-- One HSM step from a leaf `s` on event `e`: (action trace, new leaf). -/
def stepTrace (s : State) (e : Event) : List Action × State :=
  dispatchChain (ancestors 6 s) e s

/-- The new leaf only (projection of `stepTrace`). -/
def step (s : State) (e : Event) : State := (stepTrace s e).2

/-- The action trace only (projection of `stepTrace`). -/
def trace (s : State) (e : Event) : List Action := (stepTrace s e).1

/-- The initial leaf configuration after instantiation of the top state. -/
def initialLeaf : State := completeToLeaf 6 SuperSuper

/-- The instantiation entry trace: enter down from the root to the first leaf. -/
def initTrace : List Action :=
  enter SuperSuper :: enterChain SuperSuper SuperSuper

/-! ## The `Super21` precondition guard

  Chart annotation:
    Super21: precondition: (_currentState[state:Super2] && ! _currentState[state:Super1]);
  i.e. Super21 may be active only when Super2 is active and Super1 is not.
-/

/-- The guard predicate evaluated against a configuration leaf. -/
def super21Precondition (leaf : State) : Bool :=
  active leaf Super2 && ! (active leaf Super1)

/-- All states, for finite enumeration in decidable `∀` checks. -/
def allStates : List State :=
  [SuperSuper, Super2, Super21, S211, Super1, S11]

/-- All leaf states (the possible configurations). -/
def allLeaves : List State := allStates.filter isLeaf

/-! ## Structural sanity checks -/

-- Instantiation descends SuperSuper -> Super2 -> Super21 -> S211.
example : initialLeaf = S211 := by native_decide

-- Active-state set at the deepest configuration.
example : ancestors 6 S211 = [S211, Super21, Super2, SuperSuper] := by
  native_decide

-- LCA checks.
example : lca Super21 S11 = SuperSuper := by native_decide
example : lca S211 Super21 = Super21 := by native_decide
example : lca S11 S211 = SuperSuper := by native_decide

/-! ## The property from the Test block

  Firing event G from the deepest configuration `S211` (active set
  {SuperSuper, Super2, Super21, S211}) must settle the machine into
  {SuperSuper, Super1, S11}, i.e. leaf `S11`, and must leave S211.
-/

/-- Event G from S211 lands on leaf S11. -/
theorem G_from_S211_reaches_S11 : step S211 G = S11 := by native_decide

/-- The resulting active set is exactly {S11, Super1, SuperSuper}. -/
theorem G_from_S211_active_set :
    ancestors 6 (step S211 G) = [S11, Super1, SuperSuper] := by native_decide

/-- S211 is no longer active after the G step. -/
theorem G_from_S211_leaves_S211 :
    S211 ∉ ancestors 6 (step S211 G) := by native_decide

/-- The full Test-block scenario, starting from instantiation. -/
theorem test_scenario : step initialLeaf G = S11 := by native_decide

/-! ### The entry/exit action trace (the `chanltl` sequence)

  The chart's abbreviated trace for G from the initial configuration is:
    Enter Super2; Enter Super21; Enter S211;      (instantiation)
    G;
    Exit  Super2;                                  (abbreviates the exit chain)
    Enter Super1; Enter S11; (Enter S11)           (S11 doubled in source)

  Our model emits the *precise* UML chain. Instantiation enters the full path;
  the G transition (src Super21, tgt S11, LCA SuperSuper) exits S211, Super21,
  Super2 then enters Super1, S11.
-/

/-- Instantiation entry trace: enter Super2, Super21, S211 in order. -/
theorem instantiation_trace :
    initTrace = [enter SuperSuper, enter Super2, enter Super21, enter S211] := by
  native_decide

/-- Precise exit/enter trace for G from the deepest configuration. -/
theorem G_trace :
    trace S211 G =
      [exit S211, exit Super21, exit Super2, enter Super1, enter S11] := by
  native_decide

/-! ### The precondition guard holds whenever Super21 is active

  For every reachable leaf whose active set contains Super21, the guard
  `in Super2 && not in Super1` is true. The only such leaf is S211.
-/

/-- Enumerate guard validity: for every state, whenever Super21 is active the
    precondition `in Super2 && not in Super1` holds. Checked over `allStates`. -/
theorem super21_guard_sound :
    allStates.all (fun leaf =>
      ! (active leaf Super21) || super21Precondition leaf) = true := by
  native_decide

/-- The same, stated per-leaf as an implication, proved by enumeration. -/
theorem super21_guard_sound' :
    ∀ leaf ∈ allStates,
      active leaf Super21 = true → super21Precondition leaf = true := by
  decide

/-- Concretely, at S211 the guard holds; and Super21 is active exactly at S211. -/
example : super21Precondition S211 = true := by native_decide
example : active S211 Super21 = true := by native_decide
example : active S11  Super21 = false := by native_decide

/-! ## A few more semantic spot-checks -/

-- G at S11 is handled locally by S11 -> S211 (innermost handler wins).
example : step S11 G = S211 := by native_decide

-- E is only handled at the root; from any leaf it drives to S11.
example : step S211 E = S11 := by native_decide
example : step S11  E = S11 := by native_decide

-- A is a self-transition on Super21: from S211, re-enters Super21 -> S211.
example : step S211 A = S211 := by native_decide

-- An unhandled event leaves the configuration unchanged (B only on Super21).
example : step S11 B = S11 := by native_decide

end SamekHSM

