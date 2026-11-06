import Calderon.NativeSmoothMultiplierCommonSupportJets
import Calderon.NativeSmoothMultiplierForcingCoefficients
import Calderon.NativeCoefficientH1ProductTopology

/-! Smoothness is obtained
from actual coefficient functions and exact native jet graphs, not an output premise. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume

attribute [local irreducible] nativeCoefficientH1ProductL coefficientMultiplier unitBallCoordinateGradientL

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma contDiff_nativeBulkMultiplierCommutatorForcingL_of_joint_graphs
    (hcalc : FixedSobolevCalculus)
    (A : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (b : P × R3 → R3) (q : P × R3 → ℝ)
    (hA : ContDiff ℝ ∞ A) (hb : ContDiff ℝ ∞ b) (hq : ContDiff ℝ ∞ q)
    (K : Set R3) (hK : IsCompact K)
    (hAz : ∀ p x, x ∉ K → A (p,x) = 0) (hbz : ∀ p x, x ∉ K → b (p,x) = 0)
    (F : P → SmoothCoefficientMatrix 2) (G : P → Fin 3 → SmoothCoefficientJets 1)
    (Q : P → SmoothCoefficientJets 3)
    (hF : ∀ p, coefficientMatrixField 2 (F p) = fun x => A (p,x))
    (hG : ∀ p, nativeSmoothDriftField (G p) = fun x => b (p,x))
    (hQ : ∀ p, coefficientValue 3 (Q p) = fun x => q (p,x)) :
    ContDiff ℝ ∞ (fun p => nativeBulkMultiplierCommutatorForcingL hcalc (F p) (G p) (Q p)) := by
  let C : Fin 3 → P × R3 → ℝ := fun i z =>
    ∑ j : Fin 3, A z i j * smoothMultiplierSpatialDerivative q j z
  let R : Fin 3 → P × R3 → ℝ := fun j z =>
    ∑ i : Fin 3, A z i j * smoothMultiplierSpatialDerivative q i z
  let d : P × R3 → ℝ := fun z =>
    ∑ i : Fin 3, b z i * smoothMultiplierSpatialDerivative q i z
  have hC (i : Fin 3) : ContDiff ℝ ∞ (C i) :=
    ContDiff.sum (fun j hj => ((contDiff_pi.mp (contDiff_pi.mp hA i) j).mul
      (contDiff_smoothMultiplierSpatialDerivative q hq j)))
  have hR (j : Fin 3) : ContDiff ℝ ∞ (R j) :=
    ContDiff.sum (fun i hi => ((contDiff_pi.mp (contDiff_pi.mp hA i) j).mul
      (contDiff_smoothMultiplierSpatialDerivative q hq i)))
  have hd : ContDiff ℝ ∞ d :=
    ContDiff.sum (fun i hi => ((((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff).comp hb).mul
      (contDiff_smoothMultiplierSpatialDerivative q hq i)))
  have hCz (i : Fin 3) : ∀ p x, x ∉ K → C i (p,x) = 0 := by
    intro p x hx
    simp only [C,hAz p x hx,Matrix.zero_apply,zero_mul,Finset.sum_const_zero]
  have hRz (j : Fin 3) : ∀ p x, x ∉ K → R j (p,x) = 0 := by
    intro p x hx
    simp only [R,hAz p x hx,Matrix.zero_apply,zero_mul,Finset.sum_const_zero]
  have hdz : ∀ p x, x ∉ K → d (p,x) = 0 := by
    intro p x hx
    simp only [d,hbz p x hx,PiLp.zero_apply,zero_mul,Finset.sum_const_zero]
  have hFv (p : P) (i j : Fin 3) (x : R3) :
      coefficientValue 2 (F p i j) x = A (p,x) i j :=
    congrArg (fun Z : R3 → Matrix (Fin 3) (Fin 3) ℝ => Z x i j) (hF p)
  have hGv (p : P) (i : Fin 3) (x : R3) : coefficientValue 1 (G p i) x = b (p,x) i := by
    have hv := congrArg (fun Z : R3 → R3 => Z x i) (hG p)
    exact (nativeSmoothDriftField_coordinate (G p) x i).symm.trans hv
  have hQv (p : P) (i : Fin 3) (x : R3) :
      (gradient (coefficientValue 3 (Q p)) x) i = smoothMultiplierSpatialDerivative q i (p,x) :=
    (congrArg (fun f : R3 → ℝ => (gradient f x) i) (hQ p)).trans
      (smoothMultiplierSpatialDerivative_eq_slice_gradient q hq i p x).symm
  have heC (p : P) (i : Fin 3) : smoothMultiplierColumnJets (F p) (Q p) i =
      commonSupportCoefficientFamily 2 (C i) (hC i) K hK (hCz i) p := by
    apply smoothCoefficientJets_eq_of_coefficientValue_eq 2
    funext x
    rw [coefficientValue_smoothMultiplierColumnJets,coefficientValue_commonSupportCoefficientFamily]
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg₂ (fun u v : ℝ => u*v) (hFv p i j x) (hQv p j x)
  have heR (p : P) (j : Fin 3) : smoothMultiplierRowJets (F p) (Q p) j =
      commonSupportCoefficientFamily 1 (R j) (hR j) K hK (hRz j) p := by
    apply smoothCoefficientJets_eq_of_coefficientValue_eq 1
    funext x
    rw [coefficientValue_smoothMultiplierRowJets,coefficientValue_commonSupportCoefficientFamily]
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg₂ (fun u v : ℝ => u*v) (hFv p i j x) (hQv p i x)
  have hed (p : P) : smoothMultiplierDriftJets (G p) (Q p) =
      commonSupportCoefficientFamily 1 d hd K hK hdz p := by
    apply smoothCoefficientJets_eq_of_coefficientValue_eq 1
    funext x
    rw [coefficientValue_smoothMultiplierDriftJets,coefficientValue_commonSupportCoefficientFamily]
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg₂ (fun u v : ℝ => u*v) (hGv p i x) (hQv p i x)
  have hcolumn (i : Fin 3) : ContDiff ℝ ∞ (fun p : P =>
      (unitBallCoordinateGradientL i).comp
        (nativeCoefficientH1ProductL hcalc (smoothMultiplierColumnJets (F p) (Q p) i))) := by
    have hcommon : ContDiff ℝ ∞ (fun p : P => nativeCoefficientH1ProductL hcalc
        (commonSupportCoefficientFamily 2 (C i) (hC i) K hK (hCz i) p)) :=
      contDiff_nativeCoefficientH1ProductL_commonSupport hcalc (C i) (hC i) K hK (hCz i)
    have he : (fun p : P => nativeCoefficientH1ProductL hcalc
        (commonSupportCoefficientFamily 2 (C i) (hC i) K hK (hCz i) p)) =
        (fun p : P => nativeCoefficientH1ProductL hcalc
          (smoothMultiplierColumnJets (F p) (Q p) i)) := by
      funext p
      exact congrArg (nativeCoefficientH1ProductL hcalc) (heC p i).symm
    have hmul : ContDiff ℝ ∞ (fun p : P => nativeCoefficientH1ProductL hcalc
        (smoothMultiplierColumnJets (F p) (Q p) i)) := by
      exact he ▸ hcommon
    exact contDiff_const.clm_comp hmul
  have hrow (j : Fin 3) : ContDiff ℝ ∞ (fun p : P =>
      (coefficientMultiplier hcalc 0 (smoothMultiplierRowJets (F p) (Q p) j)).comp
        (unitBallCoordinateGradientL j)) := by
    have he : (fun p => coefficientMultiplier hcalc 0 (smoothMultiplierRowJets (F p) (Q p) j)) =
        fun p => coefficientMultiplier hcalc 0
          (commonSupportCoefficientFamily 1 (R j) (hR j) K hK (hRz j) p) := by
      funext p
      exact congrArg (coefficientMultiplier hcalc 0) (heR p j)
    have hm : ContDiff ℝ ∞ (fun p : P =>
        coefficientMultiplier hcalc 0 (smoothMultiplierRowJets (F p) (Q p) j)) :=
      he.symm ▸ (contDiff_commonSupport_actual_coefficientMultiplier hcalc 0 (R j) (hR j) K hK (hRz j))
    exact hm.clm_comp contDiff_const
  have hdrift : ContDiff ℝ ∞ (fun p : P =>
      (coefficientMultiplier hcalc 0 (smoothMultiplierDriftJets (G p) (Q p))).comp
        (TauCeti.W1p.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2))) := by
    have he : (fun p => coefficientMultiplier hcalc 0 (smoothMultiplierDriftJets (G p) (Q p))) =
        fun p => coefficientMultiplier hcalc 0 (commonSupportCoefficientFamily 1 d hd K hK hdz p) := by
      funext p
      exact congrArg (coefficientMultiplier hcalc 0) (hed p)
    have hm : ContDiff ℝ ∞ (fun p : P =>
        coefficientMultiplier hcalc 0 (smoothMultiplierDriftJets (G p) (Q p))) :=
      he.symm ▸ (contDiff_commonSupport_actual_coefficientMultiplier hcalc 0 d hd K hK hdz)
    exact hm.clm_comp contDiff_const
  unfold nativeBulkMultiplierCommutatorForcingL nativeSmoothMultiplierForcingL
  exact ((ContDiff.sum (fun i hi => hcolumn i)).add
    (ContDiff.sum (fun j hj => hrow j))).sub hdrift

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_nativeBulkMultiplierCommutatorForcingL_of_joint_graphs
