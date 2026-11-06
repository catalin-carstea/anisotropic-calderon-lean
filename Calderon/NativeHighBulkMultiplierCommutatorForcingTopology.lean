import Calderon.NativeSmoothMultiplierForcingTopology
import Calderon.NativeHighSmoothMultiplierForcingTopology

/-! SAME actual column/row/drift functions at high native order. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume

attribute [local irreducible] nativeCoefficientH1ProductL coefficientMultiplier unitBallCoordinateGradientL

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma contDiff_nativeHighBulkMultiplierCommutatorForcingL_of_joint_graphs
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
    ContDiff ℝ ∞ (fun p => nativeHighBulkMultiplierCommutatorForcingL hcalc (F p) (G p) (Q p)) := by
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
  have hColumnValue (p : P) (i : Fin 3) :
      coefficientValue 2 (smoothMultiplierColumnJets (F p) (Q p) i) = fun x => C i (p,x) := by
    funext x
    rw [coefficientValue_smoothMultiplierColumnJets]
    exact Finset.sum_congr rfl (fun j _ =>
      congrArg₂ (fun u v : ℝ => u*v) (hFv p i j x) (hQv p j x))
  have hRowValue (p : P) (j : Fin 3) :
      coefficientValue 1 (smoothMultiplierRowJets (F p) (Q p) j) = fun x => R j (p,x) := by
    funext x
    rw [coefficientValue_smoothMultiplierRowJets]
    exact Finset.sum_congr rfl (fun i _ =>
      congrArg₂ (fun u v : ℝ => u*v) (hFv p i j x) (hQv p i x))
  have hDriftValue (p : P) :
      coefficientValue 1 (smoothMultiplierDriftJets (G p) (Q p)) = fun x => d (p,x) := by
    funext x
    rw [coefficientValue_smoothMultiplierDriftJets]
    exact Finset.sum_congr rfl (fun i _ =>
      congrArg₂ (fun u v : ℝ => u*v) (hGv p i x) (hQv p i x))
  exact contDiff_nativeHighSmoothMultiplierForcingL_of_value_graphs hcalc C R d hC hR hd
    K hK hCz hRz hdz (fun p => smoothMultiplierColumnJets (F p) (Q p))
    (fun p => smoothMultiplierRowJets (F p) (Q p)) (fun p => smoothMultiplierDriftJets (G p) (Q p))
    hColumnValue hRowValue hDriftValue

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_nativeHighBulkMultiplierCommutatorForcingL_of_joint_graphs
