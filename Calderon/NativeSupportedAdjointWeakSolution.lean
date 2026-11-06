import Calderon.NativeSupportedAdjointH2Regularity
import Calderon.NativeZeroEnergyAdjointInverse
import Calderon.NativeCoefficientWeakInverse
import TauCeti.Analysis.PDE.EnergyForm.Linearity

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Gradient Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic MetricVolume
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-! The actual adjoint solution is derived from original invertibility. -/

def nativeSupportedDriftSmoothData (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) :
    Fin 3 → SmoothData :=
  fun i => ⟨fun x => beta x i, (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hbeta⟩

lemma nativeAdjointDriftField_supported_eq (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) :
    nativeAdjointDriftField (nativeSupportedDriftSmoothData beta hbeta) = beta := by
  funext x
  apply PiLp.ext
  intro i
  rfl

lemma nativeDriftDivergence_supported_eq (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) :
    nativeDriftDivergence (nativeSupportedDriftSmoothData beta hbeta) =
      nativeSupportedDriftDivergence beta := by
  funext x
  exact (nativeSupportedDriftDivergence_eq_sum_gradient beta x).symm

lemma memLp_nativeEnergyIntegrand_add_lower (a : MatrixField)
    (hprincipal : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (b : R3 → R3) (c : R3 → ℝ) (hb : Continuous b) (hc : Continuous c) :
    MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens) := by
  have hlower := memLp_nativeEnergyIntegrand_of_continuous (fun _ => 0) b c
    continuous_const hb hc
  have hsum := hprincipal.add hlower
  have he : (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) =
      (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0 +
        TauCeti.PDE.energyIntegrand 0 (b x) (c x)) := by
    funext x
    simpa only [add_zero,zero_add] using
      TauCeti.PDE.energyIntegrand_add (a x) 0 0 (b x) 0 (c x)
  exact he.symm ▸ hsum

def nativeSupportedOriginalEnergyMemLp (a : MatrixField)
    (hprincipal : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (C : SmoothCoefficientJets 1) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) :
    MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (beta x) (coefficientValue 1 C x)) ⊤
      ((volume : Measure R3).restrict ballOpens) :=
  memLp_nativeEnergyIntegrand_add_lower a hprincipal beta (coefficientValue 1 C)
    hbeta.continuous (contDiff_coefficientValue 1 C).continuous

def nativeSupportedAdjointEnergyMemLp (a : MatrixField)
    (hprincipal : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (C : SmoothCoefficientJets 1) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) :
    MemLp (fun x => TauCeti.PDE.energyIntegrand (a x)ᵀ (-beta x)
      (coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)) ⊤
      ((volume : Measure R3).restrict ballOpens) := by
  have hdiv : Continuous (nativeSupportedDriftDivergence beta) :=
    (nativeDriftDivergence_supported_eq beta hbeta) ▸
      continuous_nativeDriftDivergence (nativeSupportedDriftSmoothData beta hbeta)
  exact memLp_nativeEnergyIntegrand_add_lower (fun x => (a x)ᵀ)
    (memLp_nativePrincipalTransposeIntegrand a hprincipal) (-beta)
    (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
    hbeta.continuous.neg ((contDiff_coefficientValue 1 C).continuous.sub hdiv)

def nativeSupportedOriginalZeroEnergyL (a : MatrixField)
    (hprincipal : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (C : SmoothCoefficientJets 1) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) :
    BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
  nativeZeroCoefficientEnergyL a beta (coefficientValue 1 C)
    (nativeSupportedOriginalEnergyMemLp a hprincipal C beta hbeta)

def nativeSupportedAdjointZeroEnergyL (a : MatrixField)
    (hprincipal : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (C : SmoothCoefficientJets 1) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) :
    BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
  nativeZeroCoefficientEnergyL (fun x => (a x)ᵀ) (-beta)
    (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
    (nativeSupportedAdjointEnergyMemLp a hprincipal C beta hbeta)

attribute [local irreducible] nativeZeroCoefficientEnergyL nativeZeroFunctionalInverse

lemma nativeSupportedAdjointZeroEnergyL_flip (τ0 : UnitBallValueTrace) (a : MatrixField)
    (hprincipal : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (C : SmoothCoefficientJets 1) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) :
    nativeSupportedAdjointZeroEnergyL a hprincipal C beta hbeta =
      (nativeSupportedOriginalZeroEnergyL a hprincipal C beta hbeta).flip := by
  let G := nativeSupportedDriftSmoothData beta hbeta
  have hb : nativeAdjointDriftField G = beta := nativeAdjointDriftField_supported_eq beta hbeta
  have hd : nativeDriftDivergence G = nativeSupportedDriftDivergence beta :=
    nativeDriftDivergence_supported_eq beta hbeta
  have ho : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x)
      (nativeAdjointDriftField G x) (coefficientValue 1 C x)) ⊤
      ((volume : Measure R3).restrict ballOpens) :=
    hb.symm ▸ nativeSupportedOriginalEnergyMemLp a hprincipal C beta hbeta
  have ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x)ᵀ
      (-nativeAdjointDriftField G x) (coefficientValue 1 C x-nativeDriftDivergence G x)) ⊤
      ((volume : Measure R3).restrict ballOpens) := by
    simpa only [hb,hd] using nativeSupportedAdjointEnergyMemLp a hprincipal C beta hbeta
  have he := nativeZeroCoefficientEnergyL_adjoint_flip τ0 a G (coefficientValue 1 C) ho ha
  simp only [hb,hd,Pi.neg_apply] at he
  unfold nativeSupportedAdjointZeroEnergyL nativeSupportedOriginalZeroEnergyL
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at he ⊢
  exact he

lemma nativeSupportedAdjointZeroEnergyL_isInvertible (τ0 : UnitBallValueTrace) (a : MatrixField)
    (hprincipal : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (C : SmoothCoefficientJets 1) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (hA : (nativeSupportedOriginalZeroEnergyL a hprincipal C beta hbeta).IsInvertible) :
    (nativeSupportedAdjointZeroEnergyL a hprincipal C beta hbeta).IsInvertible :=
  nativeZeroEnergy_isInvertible_of_flip_eq _ _
    (nativeSupportedAdjointZeroEnergyL_flip τ0 a hprincipal C beta hbeta) hA

lemma nativeZeroFunctionalInverse_forcing_norm_le
    (A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero) (f : BallSobolev 0) :
    ‖nativeZeroFunctionalInverse A
      (TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) f)‖ ≤
      ‖nativeZeroFunctionalInverse A‖ * ‖f‖ := by
  exact ((nativeZeroFunctionalInverse A).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (TauCeti.PDE.norm_dirichletForcing_le f) (norm_nonneg _))

lemma nativeZeroCoefficientEnergyL_eval_to_H1
    (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) (u v : BallH1Zero) :
    nativeZeroCoefficientEnergyL a b c hcoeff u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        a b c (u : BallH1) (v : BallH1) :=
  (nativeZeroCoefficientEnergyL_apply a b c hcoeff u v).trans
    (TauCeti.PDE.energyFormH1L0_apply (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := a) (b := b) (c := c) hcoeff u v)

lemma nativeZeroEnergyInverse_isWeakSolution (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (hA : (nativeZeroCoefficientEnergyL a b c hcoeff).IsInvertible) (f : BallSobolev 0) :
    TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3)) (Omega := ballOpens) a b c f
      (nativeZeroFunctionalInverse (nativeZeroCoefficientEnergyL a b c hcoeff)
        (TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) f)) := by
  intro v
  have hs := nativeZeroFunctionalInverse_self (nativeZeroCoefficientEnergyL a b c hcoeff) hA
    (TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) f) v
  exact (nativeZeroCoefficientEnergyL_eval_to_H1 a b c hcoeff _ v).symm.trans hs

lemma norm_two_lower_residual_le
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (M B : X →L[ℝ] Y) (u : X) (f : Y) :
    ‖u‖ + ‖f-M u-B u‖ ≤ (1+‖M‖+‖B‖)*‖u‖+‖f‖ := by
  have ht := norm_sub_le (f-M u) (B u)
  have hs := norm_sub_le f (M u)
  have hm := M.le_opNorm u
  have hb := B.le_opNorm u
  nlinarith

lemma norm_native_two_lower_residual_le
    (M B : BallH1 →L[ℝ] BallSobolev 0) (u : BallH1Zero) (f : BallSobolev 0) :
    ‖u‖ + ‖f-M (u : BallH1)-B (u : BallH1)‖ ≤
      (1+‖M‖+‖B‖)*‖u‖+‖f‖ := by
  have hg := norm_two_lower_residual_le (X := BallH1) (Y := BallSobolev 0)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hg
  exact hg M B (u : BallH1) f

lemma mul_residual_bound_composition
    (R L B n r f : ℝ) (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hn : n ≤ B*f) (hr : n+r ≤ L*n+f) :
    R*(n+r) ≤ (R*(L*B+1))*f := by
  calc
    _ ≤ R*(L*n+f) := mul_le_mul_of_nonneg_left hr hR
    _ ≤ R*(L*(B*f)+f) :=
      mul_le_mul_of_nonneg_left (by linarith [mul_le_mul_of_nonneg_left hn hL]) hR
    _ = _ := by ring

lemma exists_nativeSupportedAdjoint_weakSolution
    (τ0 : UnitBallValueTrace) (a : MatrixField)
    (hprincipal : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (C : SmoothCoefficientJets 1) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (hA : (nativeSupportedOriginalZeroEnergyL a hprincipal C beta hbeta).IsInvertible) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ f : BallSobolev 0, ∃ u : BallH1Zero,
      TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => (a x)ᵀ) (-beta)
        (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x) f u ∧
      ‖u‖ ≤ B * ‖f‖ := by
  let A := nativeSupportedAdjointZeroEnergyL a hprincipal C beta hbeta
  have hAdj : A.IsInvertible := nativeSupportedAdjointZeroEnergyL_isInvertible
    τ0 a hprincipal C beta hbeta hA
  refine ⟨‖nativeZeroFunctionalInverse A‖,norm_nonneg _,?_⟩
  intro f
  refine ⟨nativeZeroFunctionalInverse A
    (TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) f),?_,
    nativeZeroFunctionalInverse_forcing_norm_le A f⟩
  exact nativeZeroEnergyInverse_isWeakSolution (fun x => (a x)ᵀ) (-beta)
    (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
    (nativeSupportedAdjointEnergyMemLp a hprincipal C beta hbeta) hAdj f

lemma exists_nativeH2_solution_of_bounded_regularization
    (Weak : BallSobolev 0 → BallH1Zero → Prop)
    (M T : BallH1 →L[ℝ] BallSobolev 0) (B R : ℝ) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hWeak : ∀ f : BallSobolev 0, ∃ u : BallH1Zero, Weak f u ∧ ‖u‖ ≤ B*‖f‖)
    (hLift : ∀ (f : BallSobolev 0) (u : BallH1Zero), Weak f u → ∃ U : BallSobolev 2,
      TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) 1 U = (u : BallH1) ∧
      ‖U‖ ≤ R*(‖u‖+‖f-M (u : BallH1)-T (u : BallH1)‖)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ f : BallSobolev 0, ∃ (u : BallH1Zero) (U : BallSobolev 2),
      Weak f u ∧ TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) 1 U = (u : BallH1) ∧ ‖U‖ ≤ D*‖f‖ := by
  let L : ℝ := 1+‖M‖+‖T‖
  have hL : 0 ≤ L := add_nonneg (add_nonneg zero_le_one (norm_nonneg M)) (norm_nonneg T)
  refine ⟨R*(L*B+1),mul_nonneg hR (add_nonneg (mul_nonneg hL hB) zero_le_one),?_⟩
  intro f
  obtain ⟨u,hu,hunorm⟩ := hWeak f
  obtain ⟨U,hU,hUnorm⟩ := hLift f u hu
  have hResidual := norm_native_two_lower_residual_le M T u f
  have hBound := mul_residual_bound_composition R L B ‖u‖
    ‖f-M (u : BallH1)-T (u : BallH1)‖ ‖f‖ hR hL hunorm hResidual
  exact ⟨u,U,hu,hU,hUnorm.trans hBound⟩

lemma exists_nativeSupportedAdjoint_H2_solution
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (a : MatrixField) (lam Lam : ℝ)
    (hsmooth : ContDiffOn ℝ ∞ a (Metric.closedBall 0 2))
    (hell : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
    (hprincipal : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (C : SmoothCoefficientJets 1) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x, x ∉ K → beta x = 0)
    (hA : (nativeSupportedOriginalZeroEnergyL a hprincipal C beta hbeta).IsInvertible) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ f : BallSobolev 0, ∃ (u : BallH1Zero) (U : BallSobolev 2),
      TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => (a x)ᵀ) (-beta)
        (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x) f u ∧
      TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) 1 U = (u : BallH1) ∧ ‖U‖ ≤ D * ‖f‖ := by
  obtain ⟨B,hB,hWeak⟩ := exists_nativeSupportedAdjoint_weakSolution τ0 a hprincipal C beta hbeta hA
  obtain ⟨R,hR,hLift⟩ := exists_nativeSupportedAdjoint_H2_regularity_lift hcalc hreg
    a lam Lam hsmooth hell hprincipal C beta hbeta K hK hz
  exact exists_nativeH2_solution_of_bounded_regularization
    (TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (a x)ᵀ) (-beta)
      (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x))
    (nativeCoefficientMassL hcalc (nativeSupportedAdjointMassCoefficient C beta hbeta K hK hz))
    (supportedDriftL hcalc 0 (-beta) hbeta.neg K hK
      (nativeSupportedNegativeDrift_zeroOutside beta K hz)) B R hB hR hWeak hLift

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedDriftSmoothData
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeAdjointDriftField_supported_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeDriftDivergence_supported_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.memLp_nativeEnergyIntegrand_add_lower
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedOriginalEnergyMemLp
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedAdjointEnergyMemLp
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedOriginalZeroEnergyL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedAdjointZeroEnergyL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedAdjointZeroEnergyL_flip
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedAdjointZeroEnergyL_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeZeroFunctionalInverse_forcing_norm_le
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeZeroEnergyInverse_isWeakSolution
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_two_lower_residual_le
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_nativeSupportedAdjoint_weakSolution
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_nativeSupportedAdjoint_H2_solution

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeZeroCoefficientEnergyL_eval_to_H1
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_native_two_lower_residual_le
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.mul_residual_bound_composition

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_nativeH2_solution_of_bounded_regularization
