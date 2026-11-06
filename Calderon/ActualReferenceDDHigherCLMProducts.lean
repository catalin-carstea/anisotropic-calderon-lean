import Calderon.ActualReferenceDDHigherHCoframeJets
import Calderon.ActualReferenceDecomposition
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.Bilinear

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualReferenceDDHigherCLMProducts
open ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets
  ActualReferenceDecomposition PrincipalCommutator ReferenceDensityBounds

lemma coordinateFieldWordPartial_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : List (Fin 3)) (f : R3 → E) (hf : ContDiff ℝ ∞ f) :
    coordinateFieldWordPartial w (fun y => -f y) =
      fun y => -coordinateFieldWordPartial w f y := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    change directionalFDeriv (coordinateDirection k) (coordinateFieldWordPartial w (fun y => -f y)) =
      fun y => -directionalFDeriv (coordinateDirection k) (coordinateFieldWordPartial w f) y
    rw [ih]
    funext x
    simp only [directionalFDeriv,fderiv_fun_neg,ContinuousLinearMap.neg_apply]

lemma hasCoordinateWordJetBound_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (f : R3 → E) (hf : ContDiff ℝ ∞ f)
    (x : R3) (C beta : ℝ) (s : ℕ)
    (hF : HasCoordinateWordJetBound N f x C beta s) :
    HasCoordinateWordJetBound N (fun y => -f y) x C beta s := by
  intro w hw
  rw [coordinateFieldWordPartial_neg w f hf]
  simpa only [norm_neg] using hF w hw

lemma hasCoordinateWordJetBound_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (f g : R3 → E) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : R3) (C D beta : ℝ) (s : ℕ)
    (hF : HasCoordinateWordJetBound N f x C beta s)
    (hG : HasCoordinateWordJetBound N g x D beta s) :
    HasCoordinateWordJetBound N (fun y => f y-g y) x (C+D) beta s := by
  have ht := hasCoordinateWordJetBound_add N f (fun y => -g y) hf hg.neg
    x C D beta s hF (hasCoordinateWordJetBound_neg N g hg x D beta s hG)
  simpa only [sub_eq_add_neg] using ht

lemma hasCoordinateWordJetBound_raise_degree {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (f : R3 → E) (x : R3) (C beta : ℝ) (s t : ℕ)
    (hC : 0 ≤ C) (hb : 1 ≤ beta) (hst : s ≤ t)
    (hF : HasCoordinateWordJetBound N f x C beta s) :
    HasCoordinateWordJetBound N f x C beta t := by
  intro w hw
  apply (hF w hw).trans
  apply mul_le_mul_of_nonneg_left _ hC
  have hst' : s+w.length ≤ t+w.length := Nat.add_le_add_right hst _
  exact pow_le_pow_right₀ hb hst' 

lemma hasCoordinateWordJetBound_const_normed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (c : E) (x : R3) (C beta : ℝ) (hC : ‖c‖ ≤ C) (hb : 0 ≤ beta) :
    HasCoordinateWordJetBound N (fun _ => c) x C beta 0 := by
  intro w hw
  rw [coordinateFieldWordPartial_const]
  by_cases hw0 : w=[]
  · subst w
    change ‖(if []=[] then c else 0)‖ ≤ C*beta^(0+[].length)
    simpa only [if_true,List.length_nil,Nat.zero_add,pow_zero,mul_one] using hC
  · simp only [if_neg hw0,norm_zero]
    exact mul_nonneg ((norm_nonneg c).trans hC) (pow_nonneg hb _)

lemma directionalFDeriv_bilinear {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (f : R3 → E) (g : R3 → F)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (X x : R3) :
    directionalFDeriv X (fun y => B (f y) (g y)) x =
      B (directionalFDeriv X f x) (g x)+B (f x) (directionalFDeriv X g x) := by
  have hBf : ContDiff ℝ ∞ (fun y => B (f y)) := B.contDiff.comp hf
  rw [directionalFDeriv_clm_apply X (fun y => B (f y)) g hBf hg x]
  rw [directionalFDeriv_fixed_map B f hf X x]

lemma norm_bilinear_coordinateWord_value_le {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (hB : ‖B‖ ≤ 1)
    (N : ℕ) (f : R3 → E) (g : R3 → F) (x : R3)
    (C D beta : ℝ) (s t : ℕ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hb : 0 ≤ beta)
    (hF : ‖f x‖ ≤ C*beta^s) (hG : ‖g x‖ ≤ D*beta^t) :
    ‖B (f x) (g x)‖ ≤ ((2:ℝ)^N*C*D)*beta^(s+t) := by
  have hconst : C*D ≤ (2:ℝ)^N*C*D := by
    have ht := mul_le_mul_of_nonneg_right (one_le_pow₀ (show 1 ≤ (2:ℝ) by norm_num) (n := N))
      (mul_nonneg hC hD)
    simpa only [one_mul,mul_assoc] using ht
  calc
    ‖B (f x) (g x)‖ ≤ 1*(C*beta^s)*(D*beta^t) :=
      B.le_of_opNorm₂_le_of_le hB hF hG
    _ = C*D*beta^(s+t) := by rw [pow_add]; ring
    _ ≤ ((2:ℝ)^N*C*D)*beta^(s+t) :=
      mul_le_mul_of_nonneg_right hconst (pow_nonneg hb _)

lemma hasCoordinateWordJetBound_bilinear {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (hB : ‖B‖ ≤ 1)
    (N : ℕ) (f : R3 → E) (g : R3 → F)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : R3) (C D beta : ℝ) (s t : ℕ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hb : 0 ≤ beta)
    (hF : HasCoordinateWordJetBound N f x C beta s)
    (hG : HasCoordinateWordJetBound N g x D beta t) :
    HasCoordinateWordJetBound N (fun y => B (f y) (g y)) x ((2:ℝ)^N*C*D) beta (s+t) := by
  induction N generalizing f g C D s t with
  | zero =>
    intro w hw
    cases w with
    | nil =>
      exact norm_bilinear_coordinateWord_value_le B hB 0 f g x C D beta s t hC hD hb
        (by simpa only [coordinateFieldWordPartial,List.length_nil,Nat.add_zero] using hF [] (by simp))
        (by simpa only [coordinateFieldWordPartial,List.length_nil,Nat.add_zero] using hG [] (by simp))
    | cons k v => simp at hw
  | succ N ih =>
    intro w hw
    cases w with
    | nil =>
      exact norm_bilinear_coordinateWord_value_le B hB (N+1) f g x C D beta s t hC hD hb
        (by simpa only [coordinateFieldWordPartial,List.length_nil,Nat.add_zero] using hF [] (by simp))
        (by simpa only [coordinateFieldWordPartial,List.length_nil,Nat.add_zero] using hG [] (by simp))
    | cons k v =>
      have hv : v.length ≤ N := by simp only [List.length_cons] at hw; omega
      let fk : R3 → E := directionalFDeriv (coordinateDirection k) f
      let gk : R3 → F := directionalFDeriv (coordinateDirection k) g
      have hfk : ContDiff ℝ ∞ fk := contDiff_directionalFDeriv (coordinateDirection k) f hf
      have hgk : ContDiff ℝ ∞ gk := contDiff_directionalFDeriv (coordinateDirection k) g hg
      have hFk : HasCoordinateWordJetBound N fk x C beta (s+1) :=
        hasCoordinateWordJetBound_coordinate_derivative N f x C beta s k hF
      have hGk : HasCoordinateWordJetBound N gk x D beta (t+1) :=
        hasCoordinateWordJetBound_coordinate_derivative N g x D beta t k hG
      have hFt : HasCoordinateWordJetBound N f x C beta s :=
        hasCoordinateWordJetBound_truncate N (N+1) f x C beta s hF (by omega)
      have hGt : HasCoordinateWordJetBound N g x D beta t :=
        hasCoordinateWordJetBound_truncate N (N+1) g x D beta t hG (by omega)
      have h1 : HasCoordinateWordJetBound N (fun y => B (fk y) (g y)) x
          ((2:ℝ)^N*C*D) beta ((s+1)+t) :=
        ih (f := fk) (g := g) (hf := hfk) (hg := hg) (C := C) (D := D)
          (s := s+1) (t := t) (hC := hC) (hD := hD) (hF := hFk) (hG := hGt)
      have h2 : HasCoordinateWordJetBound N (fun y => B (f y) (gk y)) x
          ((2:ℝ)^N*C*D) beta (s+(t+1)) :=
        ih (f := f) (g := gk) (hf := hf) (hg := hgk) (C := C) (D := D)
          (s := s) (t := t+1) (hC := hC) (hD := hD) (hF := hFt) (hG := hGk)
      have he : directionalFDeriv (coordinateDirection k) (fun y => B (f y) (g y)) =
          fun y => B (fk y) (g y)+B (f y) (gk y) := by
        funext y
        exact directionalFDeriv_bilinear B f g hf hg (coordinateDirection k) y
      have hBg : ContDiff ℝ ∞ (fun y => B (f y) (g y)) := (B.contDiff.comp hf).clm_apply hg
      have hB1 : ContDiff ℝ ∞ (fun y => B (fk y) (g y)) := (B.contDiff.comp hfk).clm_apply hg
      have hB2 : ContDiff ℝ ∞ (fun y => B (f y) (gk y)) := (B.contDiff.comp hf).clm_apply hgk
      change ‖directionalFDeriv (coordinateDirection k)
          (coordinateFieldWordPartial v (fun y => B (f y) (g y))) x‖ ≤
        ((2:ℝ)^(N+1)*C*D)*beta^(s+t+(v.length+1))
      rw [← coordinateFieldWordPartial_coordinate_derivative_commute k v _ hBg,he,
        coordinateFieldWordPartial_add v _ _ hB1 hB2]
      have ht1 := h1 v hv
      have ht2 := h2 v hv
      have he1 : (s+1)+t+v.length=s+t+(v.length+1) := by omega
      have he2 : s+(t+1)+v.length=s+t+(v.length+1) := by omega
      rw [he1] at ht1
      rw [he2] at ht2
      calc
        ‖coordinateFieldWordPartial v (fun y => B (fk y) (g y)) x+
            coordinateFieldWordPartial v (fun y => B (f y) (gk y)) x‖ ≤
            ‖coordinateFieldWordPartial v (fun y => B (fk y) (g y)) x‖+
              ‖coordinateFieldWordPartial v (fun y => B (f y) (gk y)) x‖ := norm_add_le _ _
        _ ≤ ((2:ℝ)^N*C*D)*beta^(s+t+(v.length+1))+
              ((2:ℝ)^N*C*D)*beta^(s+t+(v.length+1)) := add_le_add ht1 ht2
        _ = ((2:ℝ)^(N+1)*C*D)*beta^(s+t+(v.length+1)) := by rw [pow_succ]; ring

lemma hasCoordinateWordJetBound_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (f : R3 → ℝ) (g : R3 → E)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : R3) (C D beta : ℝ) (s t : ℕ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hb : 0 ≤ beta)
    (hF : HasCoordinateWordJetBound N f x C beta s)
    (hG : HasCoordinateWordJetBound N g x D beta t) :
    HasCoordinateWordJetBound N (fun y => f y • g y) x ((2:ℝ)^N*C*D) beta (s+t) := by
  exact hasCoordinateWordJetBound_bilinear (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
    ContinuousLinearMap.opNorm_lsmul_le N f g hf hg x C D beta s t hC hD hb hF hG

lemma hasCoordinateWordJetBound_clm_comp {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (N : ℕ) (f : R3 → F →L[ℝ] G) (g : R3 → E →L[ℝ] F)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : R3) (C D beta : ℝ) (s t : ℕ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hb : 0 ≤ beta)
    (hF : HasCoordinateWordJetBound N f x C beta s)
    (hG : HasCoordinateWordJetBound N g x D beta t) :
    HasCoordinateWordJetBound N (fun y => (f y).comp (g y)) x ((2:ℝ)^N*C*D) beta (s+t) := by
  exact hasCoordinateWordJetBound_bilinear (ContinuousLinearMap.compL ℝ E F G)
    (ContinuousLinearMap.norm_compL_le ℝ E F G) N f g hf hg x C D beta s t hC hD hb hF hG

end OAI.AnisotropicCalderon.ActualReferenceDDHigherCLMProducts
