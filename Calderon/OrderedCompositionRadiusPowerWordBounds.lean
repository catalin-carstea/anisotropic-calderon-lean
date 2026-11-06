import Calderon.LocalCoordinateWordJetLinearOperations
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily

lemma radiusPower_smul_ordered_composition_sum
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (power : ℕ) (r f : ℝ) (T T1 : E →L[ℝ] V) (C0 : Fin 3 → E →L[ℝ] V)
    (Mi : E →L[ℝ] E) (M N : Fin 3 → E →L[ℝ] E) :
    r^power • (T.comp Mi + (∑ j : Fin 3, (C0 j).comp (N j)) +
      r • (∑ j : Fin 3, T1.comp ((M j).comp (N j))) +
      r^2 • (∑ j : Fin 3, T.comp ((M j).comp (N j))) + (r*f) • T) =
    (r^power • T).comp Mi + (∑ j : Fin 3, (C0 j).comp (r^power • N j)) +
      (∑ j : Fin 3, T1.comp ((M j).comp (r^(power+1) • N j))) +
      (∑ j : Fin 3, (r^power • T).comp ((M j).comp (r^2 • N j))) +
      f • (r^(power+1) • T) := by
  have hNext : r^power*r = r^(power+1) := (pow_succ r power).symm
  have hLast : r^power*(r*f) = f*r^(power+1) := by rw [pow_succ]; ring
  have hSquare : r^power*r^2 = r^2*r^power := mul_comm _ _
  simp only [ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul,
    smul_add,Finset.smul_sum,smul_smul,hNext,hLast,hSquare]

end OAI.AnisotropicCalderon.DirichletFamily

namespace OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets
open ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets
  ActualReferenceDDHigherCLMProducts ReferenceDensityBounds

lemma norm_coordinateFieldWordPartial_ordered_five_term_sum_radius_power_le
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (power : ℕ) (Ta Tnext D : R3 → E →L[ℝ] V) (C0 : Fin 3 → R3 → E →L[ℝ] V)
    (Na Nnext Ntwo : Fin 3 → R3 → E →L[ℝ] E) (M : Fin 3 → E →L[ℝ] E)
    (f : R3 → ℝ) (i : Fin 3) (U : Set R3) (hU : IsOpen U)
    (hTa : ContDiffOn ℝ ∞ Ta U) (hTnext : ContDiffOn ℝ ∞ Tnext U)
    (hD : ContDiffOn ℝ ∞ D U) (hC0 : ∀ j, ContDiffOn ℝ ∞ (C0 j) U)
    (hNa : ∀ j, ContDiffOn ℝ ∞ (Na j) U)
    (hNnext : ∀ j, ContDiffOn ℝ ∞ (Nnext j) U)
    (hNtwo : ∀ j, ContDiffOn ℝ ∞ (Ntwo j) U)
    (hf : ContDiffOn ℝ ∞ f U) (x : R3) (hx : x ∈ U)
    (C B F m beta eta : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) (hF : 0 ≤ F)
    (hm : ∀ j, ‖M j‖ ≤ m) (hbeta : 1 ≤ beta) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hTaB : HasCoordinateWordJetBound 3 Ta x (C*eta^power/beta^(2*power)) beta 0)
    (hTnextB : HasCoordinateWordJetBound 3 Tnext x (C*eta^(power+1)/beta^(2*(power+1))) beta 0)
    (hDB : HasCoordinateWordJetBound 3 D x B beta 0)
    (hC0B : ∀ j, HasCoordinateWordJetBound 3 (C0 j) x B beta 0)
    (hNaB : ∀ j, HasCoordinateWordJetBound 3 (Na j) x (C*eta^power/beta^(2*power)) beta 0)
    (hNnextB : ∀ j, HasCoordinateWordJetBound 3 (Nnext j) x (C*eta^(power+1)/beta^(2*(power+1))) beta 0)
    (hNtwoB : ∀ j, HasCoordinateWordJetBound 3 (Ntwo j) x (C*eta^2/beta^4) beta 0)
    (hfB : HasCoordinateWordJetBound 3 f x F beta 1)
    (word : List (Fin 3)) (hw : word.length ≤ 3) :
    ‖coordinateFieldWordPartial word (fun y =>
      (Ta y).comp (M i) + (∑ j : Fin 3, (C0 j y).comp (Na j y)) +
      (∑ j : Fin 3, (D y).comp ((M j).comp (Nnext j y))) +
      (∑ j : Fin 3, (Ta y).comp ((M j).comp (Ntwo j y))) +
      f y • Tnext y) x‖ ≤
      (C*m+24*B*C+24*B*m*C+24*C^2*m+8*F*C)*eta^power*beta^word.length/beta^(2*power) := by
  classical
  have hm0 : 0 ≤ m := (norm_nonneg (M i)).trans (hm i)
  have hb0 : 0 ≤ beta := (by norm_num : (0 : ℝ) ≤ 1).trans hbeta
  have hbp : 0 < beta := lt_of_lt_of_le zero_lt_one hbeta
  let a : ℝ := C*eta^power/beta^(2*power)
  let b : ℝ := C*eta^(power+1)/beta^(2*(power+1))
  let c : ℝ := C*eta^2/beta^4
  have hc : 0 ≤ c := div_nonneg (mul_nonneg hC (sq_nonneg eta)) (pow_nonneg hb0 _)
  have ha : 0 ≤ a := div_nonneg (mul_nonneg hC (pow_nonneg heta _)) (pow_nonneg hb0 _)
  have hb : 0 ≤ b := div_nonneg (mul_nonneg hC (pow_nonneg heta _)) (pow_nonneg hb0 _)
  let right : Fin 3 → (E →L[ℝ] V) →L[ℝ] (E →L[ℝ] V) := fun j =>
    (ContinuousLinearMap.compL ℝ E E V).flip (M j)
  let left : Fin 3 → (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) := fun j =>
    ContinuousLinearMap.compL ℝ E E E (M j)
  have hRight (j : Fin 3) : ‖right j‖ ≤ m := by
    calc
      ‖right j‖ ≤ ‖(ContinuousLinearMap.compL ℝ E E V).flip‖ * ‖M j‖ :=
        ((ContinuousLinearMap.compL ℝ E E V).flip).le_opNorm (M j)
      _ ≤ 1 * ‖M j‖ := mul_le_mul_of_nonneg_right
        ((ContinuousLinearMap.opNorm_flip _).trans_le (ContinuousLinearMap.norm_compL_le ℝ E E V))
        (norm_nonneg _)
      _ ≤ m := by simpa only [one_mul] using hm j
  have hLeft (j : Fin 3) : ‖left j‖ ≤ m := by
    calc
      ‖left j‖ ≤ ‖ContinuousLinearMap.compL ℝ E E E‖ * ‖M j‖ :=
        (ContinuousLinearMap.compL ℝ E E E).le_opNorm (M j)
      _ ≤ 1 * ‖M j‖ := mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.norm_compL_le ℝ E E E) (norm_nonneg _)
      _ ≤ m := by simpa only [one_mul] using hm j
  have hMNtwo (j : Fin 3) := hasCoordinateWordJetBound_fixed_map_of_isOpen
    (left j) 3 (Ntwo j) U hU (hNtwo j) x hx m c beta 0 (hLeft j) (hNtwoB j)
  have hMNnext (j : Fin 3) := hasCoordinateWordJetBound_fixed_map_of_isOpen
    (left j) 3 (Nnext j) U hU (hNnext j) x hx m b beta 0 (hLeft j) (hNnextB j)
  have hOne := hasCoordinateWordJetBound_fixed_map_of_isOpen
    (right i) 3 Ta U hU hTa x hx m a beta 0 (hRight i) hTaB
  have hTwo (j : Fin 3) := hasCoordinateWordJetBound_clm_comp_of_isOpen
    3 (C0 j) (Na j) U hU (hC0 j) (hNa j) x hx B a beta 0 0 hB ha hb0 (hC0B j) (hNaB j)
  have hThree (j : Fin 3) := hasCoordinateWordJetBound_clm_comp_of_isOpen
    3 D (fun y => (M j).comp (Nnext j y)) U hU hD
    (contDiffOn_const.clm_comp (hNnext j)) x hx B (m*b) beta 0 0
    hB (mul_nonneg hm0 hb) hb0 hDB (hMNnext j)
  have hFour (j : Fin 3) := hasCoordinateWordJetBound_clm_comp_of_isOpen
    3 Ta (fun y => (M j).comp (Ntwo j y)) U hU hTa
    (contDiffOn_const.clm_comp (hNtwo j)) x hx a (m*c) beta 0 0
    ha (mul_nonneg hm0 hc) hb0 hTaB (hMNtwo j)
  have hFive := hasCoordinateWordJetBound_smul_of_isOpen
    3 f Tnext U hU hf hTnext x hx F b beta 1 0 hF hb hb0 hfB hTnextB
  have hFive0 : HasCoordinateWordJetBound 3 (fun y => f y • Tnext y) x
      (((2:ℝ)^3*F*b)*beta) beta 0 := by
    intro w hw
    have h := hFive w hw
    have heq : ((2:ℝ)^3*F*b)*beta^(1+w.length) =
        (((2:ℝ)^3*F*b)*beta)*beta^(0+w.length) := by
      rw [zero_add,pow_add,pow_one]
      ring
    exact h.trans_eq heq
  have hSum2 := hasCoordinateWordJetBound_sum_of_isOpen
    3 (fun j y => (C0 j y).comp (Na j y)) U hU
    (fun j => (hC0 j).clm_comp (hNa j)) x hx ((2:ℝ)^3*B*a) beta 0 hTwo
  have hSum3 := hasCoordinateWordJetBound_sum_of_isOpen
    3 (fun j y => (D y).comp ((M j).comp (Nnext j y))) U hU
    (fun j => hD.clm_comp (contDiffOn_const.clm_comp (hNnext j)))
    x hx ((2:ℝ)^3*B*(m*b)) beta 0 hThree
  have hSum4 := hasCoordinateWordJetBound_sum_of_isOpen
    3 (fun j y => (Ta y).comp ((M j).comp (Ntwo j y))) U hU
    (fun j => hTa.clm_comp (contDiffOn_const.clm_comp (hNtwo j)))
    x hx ((2:ℝ)^3*a*(m*c)) beta 0 hFour
  have hs1 : ContDiffOn ℝ ∞ (fun y => (Ta y).comp (M i)) U :=
    hTa.clm_comp contDiffOn_const
  have hs2 : ContDiffOn ℝ ∞ (fun y => ∑ j : Fin 3, (C0 j y).comp (Na j y)) U :=
    ContDiffOn.sum (fun j _ => (hC0 j).clm_comp (hNa j))
  have hs3 : ContDiffOn ℝ ∞ (fun y => ∑ j : Fin 3, (D y).comp ((M j).comp (Nnext j y))) U :=
    ContDiffOn.sum (fun j _ => hD.clm_comp (contDiffOn_const.clm_comp (hNnext j)))
  have hs4 : ContDiffOn ℝ ∞ (fun y => ∑ j : Fin 3, (Ta y).comp ((M j).comp (Ntwo j y))) U :=
    ContDiffOn.sum (fun j _ => hTa.clm_comp (contDiffOn_const.clm_comp (hNtwo j)))
  have h12 := hasCoordinateWordJetBound_add_of_isOpen 3 _ _ U hU hs1 hs2 x hx _ _ beta 0 hOne hSum2
  have h123 := hasCoordinateWordJetBound_add_of_isOpen 3 _ _ U hU (hs1.add hs2) hs3 x hx _ _ beta 0 h12 hSum3
  have h1234 := hasCoordinateWordJetBound_add_of_isOpen 3 _ _ U hU ((hs1.add hs2).add hs3) hs4 x hx _ _ beta 0 h123 hSum4
  have hAll := hasCoordinateWordJetBound_add_of_isOpen 3 _ _ U hU (((hs1.add hs2).add hs3).add hs4)
    (hf.smul hTnext) x hx _ _ beta 0 h1234 hFive0
  have hBeta2 : 1 ≤ beta^2 := one_le_pow₀ hbeta
  have hEtaBeta : eta ≤ beta := heta1.trans hbeta
  have hEtaBeta2 : eta ≤ beta^2 := heta1.trans hBeta2
  have hRatio1 : eta/beta ≤ 1 := (div_le_one hbp).mpr hEtaBeta
  have hRatio2 : eta/beta^2 ≤ 1 := (div_le_one (pow_pos hbp 2)).mpr hEtaBeta2
  have hRatio20 : 0 ≤ eta/beta^2 := div_nonneg heta (pow_nonneg hb0 _)
  have hRatioSq : (eta/beta^2)^2 ≤ 1 := pow_le_one₀ hRatio20 hRatio2
  have hBFactor : b = a*(eta/beta^2) := by
    dsimp only [a,b]
    rw [show 2*(power+1) = 2*power+2 by omega,pow_add,pow_succ]
    field_simp [ne_of_gt hbp]
    <;> ring
  have hBBetaFactor : b*beta = a*(eta/beta) := by
    rw [hBFactor]
    field_simp [ne_of_gt hbp]
    <;> ring
  have hCFactor : c = C*(eta/beta^2)^2 := by
    dsimp only [c]
    field_simp [ne_of_gt hbp]
    <;> ring
  have hBLe : b ≤ a := by
    rw [hBFactor]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hRatio2 ha
  have hBBetaLe : b*beta ≤ a := by
    rw [hBBetaFactor]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hRatio1 ha
  have hCLe : c ≤ C := by
    rw [hCFactor]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hRatioSq hC
  have hThreeLe : 24*B*(m*b) ≤ 24*B*m*a := by
    nlinarith only [mul_le_mul_of_nonneg_left hBLe
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤24) hB) hm0)]
  have hFourLe : 24*a*(m*c) ≤ 24*C*m*a := by
    nlinarith only [mul_le_mul_of_nonneg_left hCLe
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤24) ha) hm0)]
  have hFiveLe : 8*F*b*beta ≤ 8*F*a := by
    nlinarith only [mul_le_mul_of_nonneg_left hBBetaLe
      (mul_nonneg (by norm_num : (0:ℝ)≤8) hF)]
  have hCoeff : m*a+24*B*a+24*B*(m*b)+24*a*(m*c)+8*F*b*beta ≤
      (m+24*B+24*B*m+24*C*m+8*F)*a := by
    nlinarith only [hThreeLe,hFourLe,hFiveLe]
  have hFinal := hAll word hw
  norm_num only [Fintype.card_fin,Nat.cast_ofNat,pow_succ,pow_zero,zero_add] at hFinal
  calc
    _ ≤ (m*a+24*B*a+24*B*(m*b)+24*a*(m*c)+8*F*b*beta)*beta^word.length := by
      convert hFinal using 1 <;> ring
    _ ≤ ((m+24*B+24*B*m+24*C*m+8*F)*a)*beta^word.length :=
      mul_le_mul_of_nonneg_right hCoeff (pow_nonneg hb0 _)
    _ = (C*m+24*B*C+24*B*m*C+24*C^2*m+8*F*C)*eta^power*beta^word.length/beta^(2*power) := by
      dsimp only [a]
      ring

end OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets

#print axioms OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets.norm_coordinateFieldWordPartial_ordered_five_term_sum_radius_power_le

#print axioms OAI.AnisotropicCalderon.DirichletFamily.radiusPower_smul_ordered_composition_sum
