import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1598

open PEqualNP.CircuitLowerBounds

-- a fold whose step appends exactly one element
lemma foldl_app {α β : Type} (f : List α → β → List α) (hf : ∀ l b, ∃ a, f l b = l ++ [a]) :
    ∀ (L : List β) (l : List α), ∃ t, L.foldl f l = l ++ t ∧ t.length = L.length := by
  intro L
  induction L with
  | nil => intro l; exact ⟨[], by simp, rfl⟩
  | cons b L ih =>
    intro l
    obtain ⟨a, ha⟩ := hf l b
    obtain ⟨t, ht, hl⟩ := ih (f l b)
    refine ⟨a :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht, ha]
    simp

lemma foldl_split {α β : Type} (f : List α → β → List α) (G : List β) (l : List α) (j : ℕ)
    (hj : j < G.length) :
    G.foldl f l = (G.drop (j + 1)).foldl f (f ((G.take j).foldl f l) G[j]) := by
  conv_lhs => rw [← List.take_append_drop j G]
  rw [List.foldl_append, List.drop_eq_getElem_cons hj, List.foldl_cons]

lemma len_foldl {α β : Type} (f : List α → β → List α) (hf : ∀ l b, ∃ a, f l b = l ++ [a])
    (L : List β) (l : List α) : (L.foldl f l).length = l.length + L.length := by
  obtain ⟨t, ht, hl⟩ := foldl_app f hf L l
  rw [ht, List.length_append, hl]

lemma getD_foldl_lt {α β : Type} (f : List α → β → List α) (hf : ∀ l b, ∃ a, f l b = l ++ [a])
    (L : List β) (l : List α) (d : α) (i : ℕ) (hi : i < l.length) :
    (L.foldl f l).getD i d = l.getD i d := by
  obtain ⟨t, ht, _⟩ := foldl_app f hf L l
  rw [ht]
  exact List.getD_append _ _ _ _ hi

-- reading the whole fold at an index below the prefix state before position j
lemma getD_foldl_pre {α β : Type} (f : List α → β → List α) (hf : ∀ l b, ∃ a, f l b = l ++ [a])
    (G : List β) (l : List α) (d : α) (j i : ℕ) (hj : j < G.length)
    (hi : i < ((G.take j).foldl f l).length) :
    (G.foldl f l).getD i d = ((G.take j).foldl f l).getD i d := by
  rw [foldl_split f G l j hj]
  obtain ⟨a, ha⟩ := hf ((G.take j).foldl f l) G[j]
  rw [getD_foldl_lt f hf _ _ _ _ (by rw [ha, List.length_append]; omega), ha]
  exact List.getD_append _ _ _ _ hi

-- reading the whole fold at the element added at position j
lemma getD_foldl_new {α β : Type} (f : List α → β → List α) (hf : ∀ l b, ∃ a, f l b = l ++ [a])
    (G : List β) (l : List α) (d : α) (j : ℕ) (hj : j < G.length) :
    (G.foldl f l).getD ((G.take j).foldl f l).length d =
      (f ((G.take j).foldl f l) G[j]).getD ((G.take j).foldl f l).length d := by
  rw [foldl_split f G l j hj]
  obtain ⟨a, ha⟩ := hf ((G.take j).foldl f l) G[j]
  exact getD_foldl_lt f hf _ _ _ _ (by rw [ha, List.length_append]; simp)

def stepW (W : List Bool) (g : Gate) : List Bool :=
  W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]

lemma stepW_app : ∀ (l : List Bool) (g : Gate), ∃ a, stepW l g = l ++ [a] :=
  fun _ _ => ⟨_, rfl⟩

lemma orStep_app (n : ℕ) : ∀ (l : List (List ℕ)) (g : Gate),
    ∃ a, PEqualNP.CleanedNonEdge.orStep n l g = l ++ [a] :=
  fun _ _ => ⟨_, rfl⟩

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wireVal_eq (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) :
    PEqualNP.CleanedNonEdge.wireVal n C w x = (C.gates.foldl stepW (List.ofFn x)).getD w false :=
  rfl

lemma wireVal_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    PEqualNP.CleanedNonEdge.wireVal n C w x = x ⟨w, hw⟩ := by
  rw [wireVal_eq, getD_foldl_lt stepW stepW_app _ _ _ _ (by simpa using hw)]
  rw [List.getD_eq_getElem _ _ (by simpa using hw)]
  simp

lemma wireVal_past (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : PEqualNP.CleanedNonEdge.wireVal n C w x = false := by
  rw [wireVal_eq, List.getD_eq_default]
  rw [len_foldl stepW stepW_app]
  simpa using hw

lemma pre_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    ((C.gates.take j).foldl stepW (List.ofFn x)).length = n + j := by
  rw [len_foldl stepW stepW_app]
  simp
  omega

lemma wireVal_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.CleanedNonEdge.wireVal n C (n + j) x =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        if i < n + j then PEqualNP.CleanedNonEdge.wireVal n C i x else false) := by
  have hp := pre_len n C x j hj
  have hnew := getD_foldl_new stepW stepW_app C.gates (List.ofFn x) false j hj
  rw [hp] at hnew
  rw [wireVal_eq, hnew]
  set pre := (C.gates.take j).foldl stepW (List.ofFn x) with hpre
  rw [show stepW pre C.gates[j] =
    pre ++ [C.gates[j].op.eval (C.gates[j].inputs.map fun i => pre.getD i false)] from rfl]
  rw [List.getD_append_right _ _ _ _ (by omega), hp, Nat.sub_self]
  simp only [List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  split_ifs with hi
  · rw [wireVal_eq, getD_foldl_pre stepW stepW_app _ _ _ j i hj
      (by have := pre_len n C x j hj; omega)]
  · rw [List.getD_eq_default _ _ (by omega)]

lemma orSets_eq (n : ℕ) (C : Circuit) :
    PEqualNP.CleanedNonEdge.orSets n C = C.gates.foldl (PEqualNP.CleanedNonEdge.orStep n) [] := rfl

lemma os_pre_len (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    ((C.gates.take j).foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = j := by
  rw [len_foldl _ (orStep_app n)]
  simp
  omega

-- the OR closure of gate j contains j
lemma orSets_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    j ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD j [] := by
  have hp := os_pre_len n C j hj
  have hnew := getD_foldl_new _ (orStep_app n) C.gates [] [] j hj
  rw [hp] at hnew
  rw [orSets_eq, hnew]
  set pre := (C.gates.take j).foldl (PEqualNP.CleanedNonEdge.orStep n) [] with hpre
  have hs : ∃ t, PEqualNP.CleanedNonEdge.orStep n pre C.gates[j] = pre ++ [pre.length :: t] :=
    ⟨_, rfl⟩
  obtain ⟨t, ht⟩ := hs
  rw [ht, List.getD_append_right _ _ _ _ (by omega), hp, Nat.sub_self]
  simp

-- the OR closure of an OR gate contains the closures of its earlier gate inputs
lemma orSets_or (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hor : C.gates[j].op = GateOp.or) (i : ℕ) (hi : i ∈ C.gates[j].inputs) (hni : n ≤ i)
    (hij : i < n + j) (g : ℕ) (hg : g ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD (i - n) []) :
    g ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD j [] := by
  have hp := os_pre_len n C j hj
  have hnew := getD_foldl_new _ (orStep_app n) C.gates [] [] j hj
  rw [hp] at hnew
  rw [orSets_eq] at hg ⊢
  rw [hnew]
  rw [getD_foldl_pre _ (orStep_app n) _ _ _ j (i - n) hj (by omega)] at hg
  set pre := (C.gates.take j).foldl (PEqualNP.CleanedNonEdge.orStep n) [] with hpre
  have hs : ∃ t, PEqualNP.CleanedNonEdge.orStep n pre C.gates[j] = pre ++ [pre.length :: t] ∧
      (C.gates[j].op = GateOp.or → t =
        (C.gates[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
          (fun w => pre.getD (w - n) [])) := ⟨_, rfl, fun h => if_pos h⟩
  obtain ⟨t, ht, htor⟩ := hs
  rw [ht, List.getD_append_right _ _ _ _ (by omega), hp, Nat.sub_self]
  simp only [List.getD_cons_zero]
  rw [htor hor]
  apply List.mem_cons_of_mem
  rw [List.mem_flatMap]
  exact ⟨i, List.mem_filter.2 ⟨hi, by simp; omega⟩, hg⟩

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  exact List.getD_eq_getElem _ _ hj

end PEqualNP.Outside.L_meta_1598

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1598

theorem PEqualNP.Outside.L_meta_1598 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.EdgeOwnership.AndOrOnly C → ∀ (U : Finset (Fin n)) (w : ℕ), PEqualNP.CleanedNonEdge.wireVal n C w (fun k : Fin n => decide (k ∈ U)) = true → (∀ g : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w g → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.gateVal n C g (fun l : Fin n => decide (l ∈ U)) = false) → ∃ i ∈ U, PEqualNP.CleanedNonEdge.wireVal n C w (fun r : Fin n => decide (r = i)) = true := by
  intro n C hC U w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw hcl
  by_cases h1 : w < n
  · refine ⟨⟨w, h1⟩, ?_, ?_⟩
    · rw [wireVal_input _ _ _ _ h1] at hw
      simpa using hw
    · rw [wireVal_input _ _ _ _ h1]
      simp
  by_cases h2 : n + C.gates.length ≤ w
  · rw [wireVal_past _ _ _ _ h2] at hw
    cases hw
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hj : j < C.gates.length := by omega
  rcases hC _ (List.getElem_mem hj) with hand | hor
  · exfalso
    have hr : PEqualNP.CleanedNonEdge.OrReaches n C (n + j) j := by
      refine ⟨by omega, ?_⟩
      rw [Nat.add_sub_cancel_left]
      exact orSets_self n C j hj
    have hg := hcl j hr (by rw [gateAt_eq C j hj]; exact hand)
    have e : PEqualNP.EdgeOwnership.gateVal n C j (fun l : Fin n => decide (l ∈ U)) =
        PEqualNP.CleanedNonEdge.wireVal n C (n + j) (fun k : Fin n => decide (k ∈ U)) := rfl
    rw [e, hw] at hg
    cases hg
  · rw [wireVal_gate _ _ _ _ hj, hor] at hw
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at hw
    obtain ⟨i, hi, hv⟩ := hw
    split_ifs at hv with hlt
    have hsub : ∀ g, PEqualNP.CleanedNonEdge.OrReaches n C i g →
        PEqualNP.CleanedNonEdge.OrReaches n C (n + j) g := by
      intro g hg
      obtain ⟨hni, hgm⟩ := hg
      refine ⟨by omega, ?_⟩
      rw [Nat.add_sub_cancel_left]
      exact orSets_or n C j hj hor i hi hni hlt g hgm
    obtain ⟨k, hk, hv'⟩ := ih i (by omega) hv (fun g hg hand => hcl g (hsub g hg) hand)
    refine ⟨k, hk, ?_⟩
    rw [wireVal_gate _ _ _ _ hj, hor]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
    exact ⟨i, hi, by rw [if_pos hlt]; exact hv'⟩
