/-
Copyright (c) 2021 Jordan Brown, Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jordan Brown, Thomas Browning, Patrick Lutz
-/

import data.bracket
import group_theory.subgroup.basic
import tactic.group

/-!
# Commutators of Subgroups

If `G` is a group and `H₁ H₂ : subgroup G` then the commutator `⁅H₁, H₂⁆ : subgroup G`
is the subgroup of `G` generated by the commutators `h₁ * h₂ * h₁⁻¹ * h₂⁻¹`.

## Main definitions

* `⁅g₁, g₂⁆` : the commutator of the elements `g₁` and `g₂`
    (defined by `commutator_element` elsewhere).
* `⁅H₁, H₂⁆` : the commutator of the subgroups `H₁` and `H₂`.
-/

variables {G G' F : Type*} [group G] [group G'] [monoid_hom_class F G G'] (f : F) {g₁ g₂ g₃ g : G}

lemma commutator_element_eq_one_iff_mul_comm : ⁅g₁, g₂⁆ = 1 ↔ g₁ * g₂ = g₂ * g₁ :=
by rw [commutator_element_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

lemma commutator_element_eq_one_iff_commute : ⁅g₁, g₂⁆ = 1 ↔ commute g₁ g₂ :=
commutator_element_eq_one_iff_mul_comm

lemma commute.commutator_eq (h : commute g₁ g₂) : ⁅g₁, g₂⁆ = 1 :=
commutator_element_eq_one_iff_commute.mpr h

variables (g₁ g₂ g₃ g)

@[simp] lemma commutator_element_one_right : ⁅g, (1 : G)⁆ = 1 :=
(commute.one_right g).commutator_eq

@[simp] lemma commutator_element_one_left : ⁅(1 : G), g⁆ = 1 :=
(commute.one_left g).commutator_eq

@[simp] lemma commutator_element_inv : ⁅g₁, g₂⁆⁻¹ = ⁅g₂, g₁⁆ :=
by simp_rw [commutator_element_def, mul_inv_rev, inv_inv, mul_assoc]

lemma map_commutator_element : (f ⁅g₁, g₂⁆ : G') = ⁅f g₁, f g₂⁆ :=
by simp_rw [commutator_element_def, map_mul f, map_inv f]

lemma conjugate_commutator_element : g₃ * ⁅g₁, g₂⁆ * g₃⁻¹ = ⁅g₃ * g₁ * g₃⁻¹, g₃ * g₂ * g₃⁻¹⁆ :=
map_commutator_element (mul_aut.conj g₃).to_monoid_hom g₁ g₂

namespace subgroup

/-- The commutator of two subgroups `H₁` and `H₂`. -/
instance commutator : has_bracket (subgroup G) (subgroup G) :=
⟨λ H₁ H₂, closure {g | ∃ (g₁ ∈ H₁) (g₂ ∈ H₂), ⁅g₁, g₂⁆ = g}⟩

lemma commutator_def (H₁ H₂ : subgroup G) :
  ⁅H₁, H₂⁆ = closure {g | ∃ (g₁ ∈ H₁) (g₂ ∈ H₂), ⁅g₁, g₂⁆ = g} := rfl

lemma commutator_mem_commutator {H₁ H₂ : subgroup G} {g₁ g₂ : G} (h₁ : g₁ ∈ H₁) (h₂ : g₂ ∈ H₂) :
  ⁅g₁, g₂⁆ ∈ ⁅H₁, H₂⁆ :=
subset_closure ⟨g₁, h₁, g₂, h₂, rfl⟩

lemma commutator_le {H₁ H₂ H₃ : subgroup G} :
  ⁅H₁, H₂⁆ ≤ H₃ ↔ ∀ (g₁ ∈ H₁) (g₂ ∈ H₂), ⁅g₁, g₂⁆ ∈ H₃ :=
H₃.closure_le.trans ⟨λ h a b c d, h ⟨a, b, c, d, rfl⟩, λ h g ⟨a, b, c, d, h_eq⟩, h_eq ▸ h a b c d⟩

instance commutator_normal (H₁ H₂ : subgroup G) [h₁ : H₁.normal]
  [h₂ : H₂.normal] : normal ⁅H₁, H₂⁆ :=
begin
  let base : set G := {x | ∃ (g₁ ∈ H₁) (g₂ ∈ H₂), ⁅g₁, g₂⁆ = x},
  change (closure base).normal,
  suffices h_base : base = group.conjugates_of_set base,
  { rw h_base,
    exact subgroup.normal_closure_normal },
  refine set.subset.antisymm group.subset_conjugates_of_set (λ a h, _),
  simp_rw [group.mem_conjugates_of_set_iff, is_conj_iff] at h,
  rcases h with ⟨b, ⟨c, hc, e, he, rfl⟩, d, rfl⟩,
  exact ⟨_, h₁.conj_mem c hc d, _, h₂.conj_mem e he d, (conjugate_commutator_element c e d).symm⟩,
end

lemma commutator_mono {H₁ H₂ K₁ K₂ : subgroup G} (h₁ : H₁ ≤ K₁) (h₂ : H₂ ≤ K₂) :
  ⁅H₁, H₂⁆ ≤ ⁅K₁, K₂⁆ :=
begin
  apply closure_mono,
  rintros x ⟨p, hp, q, hq, rfl⟩,
  exact ⟨p, h₁ hp, q, h₂ hq, rfl⟩,
end

lemma commutator_def' (H₁ H₂ : subgroup G) [H₁.normal] [H₂.normal] :
  ⁅H₁, H₂⁆ = normal_closure {g | ∃ (g₁ ∈ H₁) (g₂ ∈ H₂), ⁅g₁, g₂⁆ = g} :=
le_antisymm closure_le_normal_closure (normal_closure_le_normal subset_closure)

lemma commutator_comm (H₁ H₂ : subgroup G) : ⁅H₁, H₂⁆ = ⁅H₂, H₁⁆ :=
begin
  suffices : ∀ H₁ H₂ : subgroup G, ⁅H₁, H₂⁆ ≤ ⁅H₂, H₁⁆, { exact le_antisymm (this _ _) (this _ _) },
  intros H₁ H₂,
  rw commutator_le,
  intros p hp q hq,
  have h : (p * q * p⁻¹ * q⁻¹)⁻¹ ∈ ⁅H₂, H₁⁆ := subset_closure ⟨q, hq, p, hp, by group⟩,
  convert inv_mem ⁅H₂, H₁⁆ h,
  group,
end

lemma commutator_le_right (H₁ H₂ : subgroup G) [h : normal H₂] : ⁅H₁, H₂⁆ ≤ H₂ :=
commutator_le.mpr (λ g₁ h₁ g₂ h₂, H₂.mul_mem (h.conj_mem g₂ h₂ g₁) (H₂.inv_mem h₂))

lemma commutator_le_left (H₁ H₂ : subgroup G) [h : normal H₁] : ⁅H₁, H₂⁆ ≤ H₁ :=
commutator_comm H₂ H₁ ▸ commutator_le_right H₂ H₁

@[simp] lemma commutator_bot_left (H : subgroup G) : ⁅(⊥ : subgroup G), H⁆ = ⊥ :=
le_bot_iff.mp (commutator_le_left ⊥ H)

@[simp] lemma commutator_bot_right (H : subgroup G) : ⁅H, ⊥⁆ = (⊥ : subgroup G) :=
le_bot_iff.mp (commutator_le_right H ⊥)

lemma commutator_le_inf (H₁ H₂ : subgroup G) [normal H₁] [normal H₂] : ⁅H₁, H₂⁆ ≤ H₁ ⊓ H₂ :=
le_inf (commutator_le_left H₁ H₂) (commutator_le_right H₁ H₂)

lemma map_commutator {G₂ : Type*} [group G₂] (f : G →* G₂) (H₁ H₂ : subgroup G)  :
  map f ⁅H₁, H₂⁆ = ⁅map f H₁, map f H₂⁆ :=
begin
  simp_rw [le_antisymm_iff, map_le_iff_le_comap, commutator_le, mem_comap, map_commutator_element],
  split,
  { intros p hp q hq,
    exact commutator_mem_commutator (mem_map_of_mem _ hp) (mem_map_of_mem _ hq), },
  { rintros _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩,
    rw ← map_commutator_element,
    exact mem_map_of_mem _ (commutator_mem_commutator hp hq) }
end

lemma commutator_prod_prod {G₂ : Type*} [group G₂]
  (H₁ K₁ : subgroup G) (H₂ K₂ : subgroup G₂) :
  ⁅H₁.prod H₂, K₁.prod K₂⁆ = ⁅H₁, K₁⁆.prod ⁅H₂, K₂⁆ :=
begin
  apply le_antisymm,
  { rw commutator_le,
    rintros ⟨p₁, p₂⟩ ⟨hp₁, hp₂⟩ ⟨q₁, q₂⟩ ⟨hq₁, hq₂⟩,
    exact ⟨commutator_mem_commutator hp₁ hq₁, commutator_mem_commutator hp₂ hq₂⟩ },
  { rw prod_le_iff, split;
    { rw map_commutator,
      apply commutator_mono;
      simp [le_prod_iff, map_map, monoid_hom.fst_comp_inl, monoid_hom.snd_comp_inl,
        monoid_hom.fst_comp_inr, monoid_hom.snd_comp_inr ], }, }
end

/-- The commutator of direct product is contained in the direct product of the commutators.

See `commutator_pi_pi_of_fintype` for equality given `fintype η`.
-/
lemma commutator_pi_pi_le {η : Type*} {Gs : η → Type*} [∀ i, group (Gs i)]
  (H K : Π i, subgroup (Gs i)) :
  ⁅subgroup.pi set.univ H, subgroup.pi set.univ K⁆ ≤ subgroup.pi set.univ (λ i, ⁅H i, K i⁆) :=
commutator_le.mpr $ λ p hp q hq i hi, commutator_mem_commutator (hp i hi) (hq i hi)

/-- The commutator of a finite direct product is contained in the direct product of the commutators.
-/
lemma commutator_pi_pi_of_fintype {η : Type*} [fintype η] {Gs : η → Type*}
  [∀ i, group (Gs i)] (H K : Π i, subgroup (Gs i)) :
  ⁅subgroup.pi set.univ H, subgroup.pi set.univ K⁆ = subgroup.pi set.univ (λ i, ⁅H i, K i⁆) :=
begin
  classical,
  apply le_antisymm (commutator_pi_pi_le H K),
  { rw pi_le_iff, intros i hi,
    rw map_commutator,
    apply commutator_mono;
    { rw le_pi_iff,
      intros j hj,
      rintros _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩,
      by_cases h : j = i,
      { subst h, simpa using hx, },
      { simp [h, one_mem] }, }, },
end

end subgroup
