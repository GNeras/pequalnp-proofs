import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1515

open PEqualNP.CircuitLowerBounds

-- one gate appended to a wire list, as in Circuit.wires
def step (W : List Bool) (g : Gate) : List Bool :=
  W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]

-- the value a gate takes on a wire list
def gval (g : Gate) (W : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => W.getD i false)

-- the wires of a gate list on the input list x0
def wl (x0 : List Bool) (gs : List Gate) : List Bool := gs.foldl step x0

lemma wires_eq (gs : List Gate) (o : ℕ) (x0 : List Bool) :
    Circuit.wires ⟨gs, o⟩ x0 = wl x0 gs := rfl

lemma eval_eq (gs : List Gate) (o : ℕ) (x0 : List Bool) :
    Circuit.eval ⟨gs, o⟩ x0 = (wl x0 gs).getD o false := rfl

lemma wl_append (x0 : List Bool) (gs : List Gate) (g : Gate) :
    wl x0 (gs ++ [g]) = wl x0 gs ++ [gval g (wl x0 gs)] := by
  simp [wl, List.foldl_append, step, gval]

lemma foldl_step_prefix : ∀ (L : List Gate) (W : List Bool),
    ∃ t, L.foldl step W = W ++ t := by
  intro L
  induction L with
  | nil => intro W; exact ⟨[], by simp⟩
  | cons g L ih =>
    intro W
    obtain ⟨t, ht⟩ := ih (step W g)
    refine ⟨gval g W :: t, ?_⟩
    rw [List.foldl_cons, ht]
    simp [step, gval]

lemma length_foldl_step : ∀ (L : List Gate) (W : List Bool),
    (L.foldl step W).length = W.length + L.length := by
  intro L
  induction L with
  | nil => intro W; simp
  | cons g L ih =>
    intro W
    rw [List.foldl_cons, ih]
    simp [step]
    omega

lemma length_wl (x0 : List Bool) (gs : List Gate) :
    (wl x0 gs).length = x0.length + gs.length :=
  length_foldl_step gs x0

lemma getD_snoc {α : Type} (l : List α) (a d : α) (q : ℕ) :
    (l ++ [a]).getD q d = if q < l.length then l.getD q d else if q = l.length then a else d := by
  split_ifs with h1 h2
  · rw [List.getD_append _ _ _ _ h1]
  · subst h2; simp
  · rw [List.getD_eq_default]
    simp
    omega

lemma getD_prefix {α : Type} (l t : List α) (d : α) (q : ℕ) (hq : q < l.length) :
    (l ++ t).getD q d = l.getD q d :=
  List.getD_append _ _ _ _ hq

-- abstract value of a wire: a wire of the new list (left), or a constant (right)

def look (env : List (ℕ ⊕ Bool)) (q : ℕ) : (ℕ ⊕ Bool) := env.getD q (Sum.inr false)

def avVal (W : List Bool) : (ℕ ⊕ Bool) → Bool
  | Sum.inl i => W.getD i false
  | Sum.inr b => b

def lefts (l : List (ℕ ⊕ Bool)) : List ℕ := l.filterMap Sum.getLeft?

-- the gate that computes op on abstract values, constants folded
def rwGate (op : GateOp) (l : List (ℕ ⊕ Bool)) : Gate :=
  match op with
  | GateOp.and => if Sum.inr false ∈ l then ⟨GateOp.or, []⟩ else ⟨GateOp.and, lefts l⟩
  | _ => if Sum.inr true ∈ l then ⟨GateOp.and, []⟩ else ⟨GateOp.or, lefts l⟩

-- the abstract value of a gate one of whose inputs is the constant false
def simpAV (op : GateOp) (l : List (ℕ ⊕ Bool)) : (ℕ ⊕ Bool) :=
  match op with
  | GateOp.and => Sum.inr false
  | _ => if Sum.inr true ∈ l then Sum.inr true else
      match lefts l with
      | [] => Sum.inr false
      | i :: _ => Sum.inl i

lemma avVal_snoc (W : List Bool) (u : Bool) (a : (ℕ ⊕ Bool))
    (ha : ∀ i, a = Sum.inl i → i < W.length) : avVal (W ++ [u]) a = avVal W a := by
  cases a with
  | inl i => simp only [avVal]; exact getD_prefix _ _ _ _ (ha i rfl)
  | inr b => rfl

lemma all_lefts (W : List Bool) : ∀ l : List (ℕ ⊕ Bool), Sum.inr false ∉ l →
    (l.map (avVal W)).all id = ((lefts l).map fun i => W.getD i false).all id := by
  intro l
  induction l with
  | nil => intro _; simp [lefts]
  | cons a l ih =>
    intro hl
    have hl' : Sum.inr false ∉ l := fun h => hl (List.mem_cons_of_mem _ h)
    cases a with
    | inl i => simp [lefts, avVal, ih hl'] at *
    | inr b =>
      cases b
      · exact absurd (List.mem_cons_self) hl
      · simp [lefts, List.filterMap_cons, avVal] at *
        exact ih hl'

lemma any_lefts (W : List Bool) : ∀ l : List (ℕ ⊕ Bool), Sum.inr true ∉ l →
    (l.map (avVal W)).any id = ((lefts l).map fun i => W.getD i false).any id := by
  intro l
  induction l with
  | nil => intro _; simp [lefts]
  | cons a l ih =>
    intro hl
    have hl' : Sum.inr true ∉ l := fun h => hl (List.mem_cons_of_mem _ h)
    cases a with
    | inl i => simp [lefts, avVal, ih hl'] at *
    | inr b =>
      cases b
      · simp [lefts, List.filterMap_cons, avVal] at *
        exact ih hl'
      · exact absurd (List.mem_cons_self) hl

lemma rw_sem (W : List Bool) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List (ℕ ⊕ Bool)) : gval (rwGate op l) W = op.eval (l.map (avVal W)) := by
  rcases hop with rfl | rfl
  · simp only [rwGate]
    split_ifs with h
    · simp only [gval, GateOp.eval, List.map_nil, List.any_nil]
      symm
      rw [List.all_eq_false]
      exact ⟨false, List.mem_map.2 ⟨_, h, rfl⟩, by simp⟩
    · simp only [gval, GateOp.eval]
      rw [all_lefts W l h]
  · simp only [rwGate]
    split_ifs with h
    · simp only [gval, GateOp.eval, List.map_nil, List.all_nil]
      symm
      rw [List.any_eq_true]
      exact ⟨true, List.mem_map.2 ⟨_, h, rfl⟩, rfl⟩
    · simp only [gval, GateOp.eval]
      rw [any_lefts W l h]

lemma rw_ok (op : GateOp) (l : List (ℕ ⊕ Bool)) :
    ((rwGate op l).op = GateOp.and ∨ (rwGate op l).op = GateOp.or) ∧
      (rwGate op l).inputs.length ≤ l.length := by
  have hle : (lefts l).length ≤ l.length := List.length_filterMap_le _ _
  cases op <;> simp only [rwGate] <;> split_ifs <;> simp [hle]

lemma simp_sem (W : List Bool) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List (ℕ ⊕ Bool)) (hf : Sum.inr false ∈ l) (hl : l.length ≤ 2) :
    avVal W (simpAV op l) = op.eval (l.map (avVal W)) := by
  match l, hl with
  | [a], _ =>
    simp at hf
    subst hf
    rcases hop with rfl | rfl <;> simp [simpAV, avVal, GateOp.eval, lefts, List.filterMap_cons]
  | [a, b], _ =>
    simp at hf
    rcases hf with rfl | rfl
    · rcases hop with rfl | rfl
      · simp [simpAV, avVal, GateOp.eval]
      · cases b with
        | inl i => simp [simpAV, avVal, GateOp.eval, lefts, List.filterMap_cons]
        | inr c => cases c <;> simp [simpAV, avVal, GateOp.eval, lefts, List.filterMap_cons]
    · rcases hop with rfl | rfl
      · simp [simpAV, avVal, GateOp.eval]
      · cases a with
        | inl i => simp [simpAV, avVal, GateOp.eval, lefts, List.filterMap_cons]
        | inr c => cases c <;> simp [simpAV, avVal, GateOp.eval, lefts, List.filterMap_cons]

-- the shape every gate of the list has, at its position p
def Good (n h j : ℕ) (g : Gate) (p : ℕ) : Prop :=
  g.inputs.length ≤ 2 ∧ (p = j → g.op = GateOp.not ∧ ∃ r, g.inputs = (n + h) :: r) ∧
    (p ≠ j → g.op = GateOp.and ∨ g.op = GateOp.or)

-- one step of the construction, on the gate g at position p, from position h on
def tstep (n h j : ℕ) (s : List Gate × List (ℕ ⊕ Bool)) (g : Gate) (p : ℕ) : List Gate × List (ℕ ⊕ Bool) :=
  if p = h then (s.1, s.2 ++ [Sum.inr true])
  else if p = j then (s.1, s.2 ++ [Sum.inr false])
  else if j < p ∧ n + j ∈ g.inputs then (s.1, s.2 ++ [simpAV g.op (g.inputs.map (look s.2))])
  else (s.1 ++ [rwGate g.op (g.inputs.map (look s.2))], s.2 ++ [Sum.inl (n + s.1.length)])

def run (n h j : ℕ) : List Gate → ℕ → List Gate × List (ℕ ⊕ Bool) → List Gate × List (ℕ ⊕ Bool)
  | [], _, s => s
  | g :: L, p, s => run n h j L (p + 1) (tstep n h j s g p)

def Inv (n j : ℕ) (x0 : List Bool) (p : ℕ) (s : List Gate × List (ℕ ⊕ Bool)) (W : List Bool) : Prop :=
  W.length = n + p ∧ s.2.length = n + p ∧
    (∀ q, avVal (wl x0 s.1) (look s.2 q) = W.getD q false) ∧
    (∀ q i, look s.2 q = Sum.inl i → i < n + s.1.length) ∧
    (j < p → look s.2 (n + j) = Sum.inr false)

lemma look_snoc (env : List (ℕ ⊕ Bool)) (a : (ℕ ⊕ Bool)) (q : ℕ) :
    look (env ++ [a]) q =
      if q < env.length then look env q else if q = env.length then a else Sum.inr false := by
  unfold look
  exact getD_snoc _ _ _ _

lemma push_val (env : List (ℕ ⊕ Bool)) (a : (ℕ ⊕ Bool)) (W W'' : List Bool) (v : Bool)
    (hlen : env.length = W.length)
    (hold : ∀ q, avVal W'' (look env q) = W.getD q false) (hnew : avVal W'' a = v) :
    ∀ q, avVal W'' (look (env ++ [a]) q) = (W ++ [v]).getD q false := by
  intro q
  rw [look_snoc, getD_snoc, hlen]
  split_ifs
  · exact hold q
  · exact hnew
  · rfl

lemma push_lt (env : List (ℕ ⊕ Bool)) (a : (ℕ ⊕ Bool)) (B : ℕ)
    (hold : ∀ q i, look env q = Sum.inl i → i < B) (hnew : ∀ i, a = Sum.inl i → i < B) :
    ∀ q i, look (env ++ [a]) q = Sum.inl i → i < B := by
  intro q i hq
  rw [look_snoc] at hq
  split_ifs at hq
  · exact hold q i hq
  · exact hnew i hq

lemma simpAV_inl (op : GateOp) (l : List (ℕ ⊕ Bool)) (i : ℕ) (h : simpAV op l = Sum.inl i) :
    Sum.inl i ∈ l := by
  have key : ∀ k, k ∈ lefts l → Sum.inl k ∈ l := by
    intro k hk
    unfold lefts at hk
    rw [List.mem_filterMap] at hk
    obtain ⟨a, ha, hak⟩ := hk
    cases a with
    | inl b => simp at hak; subst hak; exact ha
    | inr b => simp at hak
  unfold simpAV at h
  split at h
  · cases h
  · split_ifs at h
    revert h
    cases hl : lefts l with
    | nil => intro h; cases h
    | cons k t => intro h; simp at h; subst h; exact key _ (by rw [hl]; exact List.mem_cons_self)

theorem tstep_inv (n h j : ℕ) (x0 Wfin : List Bool) (hx0 : x0.length = n)
    (hfin : Wfin.getD (n + h) false = true) (hhj : h < j)
    (g : Gate) (p : ℕ) (s : List Gate × List (ℕ ⊕ Bool)) (W : List Bool) (hg : Good n h j g p)
    (hp : h ≤ p) (hpre : ∃ t, Wfin = step W g ++ t) (hI : Inv n j x0 p s W) :
    Inv n j x0 (p + 1) (tstep n h j s g p) (step W g) := by
  obtain ⟨hW, hE, hval, hlt, hj⟩ := hI
  obtain ⟨hlen2, hjn, hop⟩ := hg
  obtain ⟨t, ht⟩ := hpre
  have hstep : step W g = W ++ [gval g W] := rfl
  have hW' : (wl x0 s.1).length = n + s.1.length := by rw [length_wl, hx0]
  -- the value of the new gate, through the abstract values of its inputs
  have hmap : g.inputs.map (fun i => W.getD i false) =
      (g.inputs.map (look s.2)).map (avVal (wl x0 s.1)) := by
    rw [List.map_map]
    exact List.map_congr_left (fun q _ => (hval q).symm)
  have hjval : j < p + 1 → p = j ∨ j < p := by omega
  unfold tstep
  split_ifs with h1 h2 h3
  · -- p = h: the gate h is true on the region
    subst h1
    have hv : gval g W = true := by
      rw [← hfin, ht, hstep, getD_prefix _ _ _ _ (by simp [hW]), getD_snoc]
      simp [hW]
    refine ⟨by simp [hstep, hW] <;> omega, by simp [hE] <;> omega, ?_, ?_, ?_⟩
    · rw [hstep]; exact push_val _ _ _ _ _ (by rw [hE, hW]) hval (by simp [avVal, hv])
    · exact push_lt _ _ _ hlt (fun i hi => by cases hi)
    · intro hjp; omega
  · -- p = j: the NOT gate is false on the region
    subst h2
    obtain ⟨hnot, r, hr⟩ := hjn rfl
    have hh : W.getD (n + h) false = true := by
      rw [← hfin, ht, hstep, List.append_assoc, getD_prefix _ _ _ _ (by omega)]
    have hv : gval g W = false := by
      simp only [gval, hnot, hr, GateOp.eval, List.map_cons, List.headD_cons, hh, Bool.not_true]
    refine ⟨by simp [hstep, hW] <;> omega, by simp [hE] <;> omega, ?_, ?_, ?_⟩
    · rw [hstep]; exact push_val _ _ _ _ _ (by rw [hE, hW]) hval (by simp [avVal, hv])
    · exact push_lt _ _ _ hlt (fun i hi => by cases hi)
    · intro _
      rw [look_snoc]
      simp [hE]
  · -- a gate after j reading j: folded away
    obtain ⟨hjp, hmem⟩ := h3
    have hop' := hop h2
    have hf : Sum.inr false ∈ g.inputs.map (look s.2) := by
      rw [← hj hjp]; exact List.mem_map_of_mem hmem
    have hv : avVal (wl x0 s.1) (simpAV g.op (g.inputs.map (look s.2))) = gval g W := by
      rw [simp_sem _ _ hop' _ hf (by simpa using hlen2), gval, hmap]
    refine ⟨by simp [hstep, hW] <;> omega, by simp [hE] <;> omega, ?_, ?_, ?_⟩
    · rw [hstep]; exact push_val _ _ _ _ _ (by rw [hE, hW]) hval hv
    · refine push_lt _ _ _ hlt (fun i hi => ?_)
      have := simpAV_inl _ _ _ hi
      obtain ⟨q, _, hq⟩ := List.mem_map.1 this
      exact hlt q i hq
    · intro _
      rw [look_snoc, if_pos (by omega)]
      exact hj hjp
  · -- every other gate: rewritten, constants folded
    have hop' := hop h2
    set g' := rwGate g.op (g.inputs.map (look s.2)) with hg'
    have hv : gval g' (wl x0 s.1) = gval g W := by
      rw [hg', rw_sem _ _ hop', gval, hmap]
    have hnewW : wl x0 (s.1 ++ [g']) = wl x0 s.1 ++ [gval g' (wl x0 s.1)] := wl_append _ _ _
    refine ⟨by simp [hstep, hW] <;> omega, by simp [hE] <;> omega, ?_, ?_, ?_⟩
    · rw [hstep, hnewW]
      refine push_val _ _ _ _ _ (by rw [hE, hW]) (fun q => ?_) ?_
      · rw [avVal_snoc _ _ _ (fun i hi => by rw [hW']; exact hlt q i hi)]
        exact hval q
      · simp only [avVal]
        rw [getD_snoc, if_neg (by omega), if_pos hW'.symm]
        exact hv
    · refine push_lt _ _ _ (fun q i hi => ?_) (fun i hi => ?_)
      · have := hlt q i hi; simp; omega
      · cases hi; simp
    · intro hjp
      have hjp' : j < p := by omega
      rw [look_snoc, if_pos (by omega)]
      exact hj hjp'

theorem run_inv (n h j : ℕ) (x0 Wfin : List Bool) (hx0 : x0.length = n)
    (hfin : Wfin.getD (n + h) false = true) (hhj : h < j) :
    ∀ (L : List Gate) (p : ℕ) (s : List Gate × List (ℕ ⊕ Bool)) (W : List Bool),
      (∀ k (hk : k < L.length), Good n h j L[k] (p + k)) → h ≤ p →
      L.foldl step W = Wfin → Inv n j x0 p s W →
      Inv n j x0 (p + L.length) (run n h j L p s) Wfin := by
  intro L
  induction L with
  | nil =>
    intro p s W _ _ hf hI
    simp only [List.foldl_nil] at hf
    subst hf
    simpa [run] using hI
  | cons g L ih =>
    intro p s W hg hp hf hI
    have hg0 : Good n h j g p := hg 0 (by simp)
    have hpre : ∃ t, Wfin = step W g ++ t := by
      obtain ⟨t, ht⟩ := foldl_step_prefix L (step W g)
      exact ⟨t, by rw [← hf, List.foldl_cons, ht]⟩
    have := ih (p + 1) (tstep n h j s g p) (step W g)
      (fun k hk => by
        have := hg (k + 1) (by simp; omega)
        have e : p + (k + 1) = p + 1 + k := by omega
        rw [e] at this
        exact this)
      (by omega) (by rw [← hf, List.foldl_cons])
      (tstep_inv n h j x0 Wfin hx0 hfin hhj g p s W hg0 hp hpre hI)
    simpa [run, Nat.add_assoc, Nat.add_comm 1 L.length] using this

lemma run_prefix (n h j : ℕ) : ∀ (L : List Gate) (p : ℕ) (s : List Gate × List (ℕ ⊕ Bool)),
    ∃ t, (run n h j L p s).1 = s.1 ++ t := by
  intro L
  induction L with
  | nil => intro p s; exact ⟨[], by simp [run]⟩
  | cons g L ih =>
    intro p s
    obtain ⟨t, ht⟩ := ih (p + 1) (tstep n h j s g p)
    have : ∃ u, (tstep n h j s g p).1 = s.1 ++ u := by
      unfold tstep
      split_ifs
      · exact ⟨[], (List.append_nil _).symm⟩
      · exact ⟨[], (List.append_nil _).symm⟩
      · exact ⟨[], (List.append_nil _).symm⟩
      · exact ⟨_, rfl⟩
    obtain ⟨u, hu⟩ := this
    exact ⟨u ++ t, by simp only [run]; rw [ht, hu, List.append_assoc]⟩

def OkG (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma run_ok (n h j : ℕ) : ∀ (L : List Gate) (p : ℕ) (s : List Gate × List (ℕ ⊕ Bool)),
    (∀ g ∈ s.1, OkG g) → (∀ k (hk : k < L.length), Good n h j L[k] (p + k)) →
    ∀ g ∈ (run n h j L p s).1, OkG g := by
  intro L
  induction L with
  | nil => intro p s hs _; simpa [run] using hs
  | cons g L ih =>
    intro p s hs hg
    have hg0 : Good n h j g p := hg 0 (by simp)
    apply ih (p + 1) (tstep n h j s g p)
    · unfold tstep
      split_ifs with h1 h2 h3
      · exact hs
      · exact hs
      · exact hs
      · intro g' hg'
        rcases List.mem_append.1 hg' with hm | hm
        · exact hs g' hm
        · simp at hm
          subst hm
          obtain ⟨hop, hlen⟩ := rw_ok g.op (g.inputs.map (look s.2))
          exact ⟨hop, by simp at hlen; exact le_trans hlen hg0.1⟩
    · intro k hk
      have := hg (k + 1) (by simp; omega)
      have e : p + (k + 1) = p + 1 + k := by omega
      rw [e] at this
      exact this

def remB (n h j : ℕ) (gp : Gate × ℕ) : Bool :=
  decide (gp.2 = h) || decide (gp.2 = j) || (decide (j < gp.2) && decide (n + j ∈ gp.1.inputs))

lemma run_count (n h j : ℕ) : ∀ (L : List Gate) (p : ℕ) (s : List Gate × List (ℕ ⊕ Bool)),
    (run n h j L p s).1.length + (L.zipIdx p).countP (remB n h j) = s.1.length + L.length := by
  intro L
  induction L with
  | nil => intro p s; simp [run]
  | cons g L ih =>
    intro p s
    have := ih (p + 1) (tstep n h j s g p)
    simp only [run, List.zipIdx_cons, List.countP_cons, List.length_cons]
    have ht : (tstep n h j s g p).1.length + (if remB n h j (g, p) = true then 1 else 0) =
        s.1.length + 1 := by
      unfold tstep remB
      split_ifs <;> simp_all
    omega

lemma countP_three {α : Type} (a b c : α → Bool)
    (hab : ∀ x, ¬(a x = true ∧ b x = true)) (hac : ∀ x, ¬(a x = true ∧ c x = true))
    (hbc : ∀ x, ¬(b x = true ∧ c x = true)) :
    ∀ l : List α, l.countP (fun x => a x || b x || c x) = l.countP a + l.countP b + l.countP c := by
  intro l
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.countP_cons, ih]
    have h1 := hab x
    have h2 := hac x
    have h3 := hbc x
    cases ha : a x <;> cases hb : b x <;> cases hc : c x <;> simp_all <;> omega

lemma count_pos {α : Type} (t : ℕ) : ∀ (l : List α) (s : ℕ), s ≤ t → t < s + l.length →
    (l.zipIdx s).countP (fun gp => decide (gp.2 = t)) = 1 := by
  intro l
  induction l with
  | nil => intro s h1 h2; simp at h2; omega
  | cons x l ih =>
    intro s h1 h2
    rw [List.zipIdx_cons, List.countP_cons]
    by_cases hst : s = t
    · subst hst
      have h0 : (l.zipIdx (s + 1)).countP (fun gp => decide (gp.2 = s)) = 0 := by
        rw [List.countP_eq_zero]
        rintro ⟨y, i⟩ hm
        have := List.mem_zipIdx hm
        simp only [decide_eq_true_eq]
        omega
      simp [h0]
    · rw [ih (s + 1) (by omega) (by simp at h2; omega)]
      simp [hst]

lemma card_eq_countP (P : Gate → ℕ → Bool) : ∀ (l : List Gate) (s : ℕ),
    (Finset.univ.filter (fun i : Fin l.length => P (l.get i) (s + i) = true)).card =
      (l.zipIdx s).countP (fun gp => P gp.1 gp.2) := by
  intro l
  induction l with
  | nil => intro s; simp
  | cons g l ih =>
    intro s
    rw [Finset.card_filter, List.zipIdx_cons, List.countP_cons, ← ih (s + 1), Finset.card_filter]
    refine Eq.trans (Fin.sum_univ_succ (n := l.length)
      (fun i : Fin (l.length + 1) => if P ((g :: l).get i) (s + ↑i) = true then 1 else 0)) ?_
    have e0 : (g :: l).get 0 = g := rfl
    have es : ∀ i : Fin l.length, (g :: l).get i.succ = l.get i := fun i => rfl
    have ei : ∀ i : Fin l.length, s + ((i.succ : Fin (l.length + 1)) : ℕ) = s + 1 + i := by
      intro i; simp; omega
    simp only [e0, es, ei, Fin.val_zero, Nat.add_zero]
    ring

end PEqualNP.Outside.L_meta_1515

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1515

theorem PEqualNP.Outside.L_meta_1515 : ∀ (n m : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (n + (h : ℕ)) :: r) →
    (∀ w : Fin m, ∃ x y : Fin n → Bool,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn y) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn y) = false) →
    ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (out' : Fin m → ℕ),
      (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates.take (h : ℕ) <+: gates' ∧
      gates'.length + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2
        ≤ gates.length ∧
      ∀ (w : Fin m) (x : Fin n → Bool),
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', out' w⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) := by
  intro n m gates out j h hops hj huniq hhj hjin hout
  have hHJ : (h : ℕ) < j := hhj
  have hHlen : (h : ℕ) < gates.length := h.isLt
  have hJlen : (j : ℕ) < gates.length := j.isLt
  have hgood : ∀ i (hi : i < gates.length), Good n h j gates[i] i := by
    intro i hi
    refine ⟨(hops _ (List.getElem_mem hi)).2, ?_, ?_⟩
    · intro hij
      have e : gates[i] = gates.get j := by simp [hij]
      rw [e]
      exact ⟨hj, hjin⟩
    · intro hij
      rcases (hops _ (List.getElem_mem hi)).1 with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · exfalso
        apply hij
        have := huniq ⟨i, hi⟩ (by simpa using h1)
        rw [← this]
  have hgoodD : ∀ k (hk : k < (gates.drop h).length), Good n h j (gates.drop h)[k] (h + k) := by
    intro k hk
    rw [List.getElem_drop]
    exact hgood _ _
  set F := run n h j (gates.drop h) h (gates.take h, (List.range (n + h)).map Sum.inl) with hF
  refine ⟨F.1, fun w => Sum.elim id (fun _ => 0) (look F.2 (out w)), ?_, ?_, ?_, ?_⟩
  · -- only AND and OR gates of fan-in at most two
    intro g hg
    refine run_ok n h j (gates.drop h) h _ ?_ hgoodD g hg
    intro g' hg'
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg'
    rw [List.getElem_take]
    have hi' : i < h := by simp at hi; omega
    have hgi := hgood i (by omega)
    exact ⟨hgi.2.2 (by omega), hgi.1⟩
  · -- the gates before h are kept
    obtain ⟨t, ht⟩ := run_prefix n h j (gates.drop h) h (gates.take h, (List.range (n + h)).map Sum.inl)
    rw [ht]
    exact List.prefix_append _ _
  · -- the count: h, j and every later reader of j are gone
    have hc := run_count n h j (gates.drop h) h (gates.take h, (List.range (n + h)).map Sum.inl)
    have hsplit := countP_three (fun gp : Gate × ℕ => decide (gp.2 = h))
      (fun gp => decide (gp.2 = j)) (fun gp => decide (j < gp.2) && decide (n + j ∈ gp.1.inputs))
      (by intro x; simp; try omega) (by intro x; simp; try omega) (by intro x; simp; try omega)
      ((gates.drop h).zipIdx h)
    have h1 := count_pos (h : ℕ) (gates.drop h) h le_rfl (by simp)
    have h2 := count_pos (j : ℕ) (gates.drop h) h (by omega) (by simp; try omega)
    have hk : (Finset.univ.filter (fun i : Fin gates.length =>
        j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card =
        ((gates.drop h).zipIdx h).countP
          (fun gp => decide ((j : ℕ) < gp.2) && decide (n + j ∈ gp.1.inputs)) := by
      have e1 := card_eq_countP (fun g p => decide ((j : ℕ) < p) && decide (n + j ∈ g.inputs)) gates 0
      have e2 : (Finset.univ.filter (fun i : Fin gates.length =>
          j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)) =
          Finset.univ.filter (fun i : Fin gates.length =>
            (decide ((j : ℕ) < 0 + i) && decide (n + j ∈ (gates.get i).inputs)) = true) := by
        apply Finset.filter_congr
        intro i _
        simp only [decide_eq_true_eq, Bool.and_eq_true, Nat.zero_add]
        exact Iff.rfl
      rw [e2, e1]
      have e3 : gates.zipIdx 0 = (gates.take h).zipIdx 0 ++ (gates.drop h).zipIdx h := by
        conv_lhs => rw [← List.take_append_drop h gates]
        rw [List.zipIdx_append]
        congr 2
        simp
      rw [e3, List.countP_append]
      have e4 : ((gates.take h).zipIdx 0).countP
          (fun gp => decide ((j : ℕ) < gp.2) && decide (n + j ∈ gp.1.inputs)) = 0 := by
        rw [List.countP_eq_zero]
        rintro ⟨g, p⟩ hm
        have := List.mem_zipIdx hm
        simp at this ⊢
        intro hjp
        omega
      rw [e4, Nat.zero_add]
    have hrem : remB n h j = fun gp : Gate × ℕ => decide (gp.2 = (h : ℕ)) || decide (gp.2 = (j : ℕ)) ||
        (decide ((j : ℕ) < gp.2) && decide (n + j ∈ gp.1.inputs)) := rfl
    rw [hrem, hsplit, h1, h2, ← hF] at hc
    rw [hk]
    simp at hc
    omega
  · -- the outputs agree where h is true
    have key : ∀ y : Fin n → Bool,
        Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn y) = true →
        ∀ q, avVal (wl (List.ofFn y) F.1) (look F.2 q) = (wl (List.ofFn y) gates).getD q false := by
      intro y hy
      have hfin : (wl (List.ofFn y) gates).getD (n + h) false = true := by
        rw [← eval_eq]; exact hy
      have hI := run_inv n h j (List.ofFn y) (wl (List.ofFn y) gates) (by simp) hfin hHJ
        (gates.drop h) h (gates.take h, (List.range (n + h)).map Sum.inl)
        (wl (List.ofFn y) (gates.take h)) hgoodD le_rfl ?_ ?_
      · exact hI.2.2.1
      · simp only [wl]
        rw [← List.foldl_append, List.take_append_drop]
      · refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [length_wl]; simp
        · simp
        · intro q
          simp only [look]
          by_cases hq : q < n + h
          · rw [List.getD_eq_getElem _ _ (by simpa using hq)]
            simp [avVal]
          · rw [List.getD_eq_default _ _ (by simp; omega)]
            simp only [avVal]
            rw [List.getD_eq_default]
            rw [length_wl]; simp; omega
        · intro q i hq
          simp only [look] at hq
          by_cases hq' : q < n + h
          · rw [List.getD_eq_getElem _ _ (by simpa using hq')] at hq
            simp at hq
            subst hq
            simp
            omega
          · rw [List.getD_eq_default _ _ (by simp; omega)] at hq
            cases hq
        · intro hjh
          omega
    intro w x hx
    cases hl : look F.2 (out w) with
    | inl i =>
      have := key x hx (out w)
      rw [hl] at this
      simp only [eval_eq, hl, Sum.elim_inl, id]
      simpa [avVal] using this
    | inr b =>
      exfalso
      obtain ⟨y1, y2, hy1, hy2, hv1, hv2⟩ := hout w
      have k1 := key y1 hy1 (out w)
      have k2 := key y2 hy2 (out w)
      rw [hl] at k1 k2
      simp only [avVal] at k1 k2
      rw [eval_eq, ← k1] at hv1
      rw [eval_eq, ← k2] at hv2
      rw [hv1] at hv2
      cases hv2
