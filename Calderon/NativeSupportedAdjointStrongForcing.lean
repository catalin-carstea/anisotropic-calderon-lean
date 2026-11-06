import Calderon.NativeSupportedAdjointH2Regularity
import Calderon.OrdinaryWeightedDriftOperator
import Calderon.NativeWeightedDriftFluxGreen
import Calderon.LpInheritedStructureData
import Calderon.NativeCoefficientWeakInverse

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-! Full upfront expansion: native-supported-adjoint-strong-forcing-author-oct14-v001/EXPANSION-v001.json.
This is actual H2-to-L2 forcing and its proved zero-test energy identity. -/

def nativePrincipalTransposeJets (F : SmoothCoefficientMatrix 2) : SmoothCoefficientMatrix 2 :=
  fun i j => F j i

lemma coefficientMatrixField_nativePrincipalTransposeJets (F : SmoothCoefficientMatrix 2) :
    coefficientMatrixField 2 (nativePrincipalTransposeJets F) =
      (fun x => (coefficientMatrixField 2 F x)ᵀ) := rfl

def nativeH2ThreeTermForcingL (P : BallSobolev 2 →L[ℝ] BallSobolev 0)
    (D M : BallH1 →L[ℝ] BallSobolev 0) (J : BallSobolev 2 →L[ℝ] BallH1) :
    BallSobolev 2 →L[ℝ] BallSobolev 0 := (P+D.comp J)+M.comp J

lemma nativeH2ThreeTermForcingL_eq_raw (P : BallSobolev 2 →L[ℝ] BallSobolev 0)
    (D M : BallH1 →L[ℝ] BallSobolev 0) (J : BallSobolev 2 →L[ℝ] BallH1) :
    nativeH2ThreeTermForcingL P D M J = (P+D.comp J)+M.comp J := rfl

lemma nativeH2ThreeTermForcingL_apply (P : BallSobolev 2 →L[ℝ] BallSobolev 0)
    (D M : BallH1 →L[ℝ] BallSobolev 0) (J : BallSobolev 2 →L[ℝ] BallH1) (U : BallSobolev 2) :
    nativeH2ThreeTermForcingL P D M J U = P U+D (J U)+M (J U) := rfl

def nativeH2FirstOrderL : BallSobolev 2 →L[ℝ] BallH1 := by
  let L : BallSobolev 2 →ₗ[ℝ] BallH1 :=
    { toFun := TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 1
      map_add' := fun U V =>
        (TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 1).map_add U V
      map_smul' := fun c U => by
        have hm := (TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3))
          (Omega := ballOpens) (p := 2) 1).map_smul c U
        simpa only [RingHom.id_apply, TauCeti.Wkp.firstOrder,
          real_nontriviallyNormedField_normedField_eq,
          submodule_normedSpace_module_eq] using hm }
  exact L.mkContinuous 1 (fun U => by
    have hLU : L U = TauCeti.Wkp.firstOrder (mu := (volume : Measure R3))
        (Omega := ballOpens) (p := 2) 1 U := rfl
    rw [hLU, one_mul]
    exact norm_unitBall_firstOrder_le 1 U)

lemma nativeH2FirstOrderL_apply (U : BallSobolev 2) :
    nativeH2FirstOrderL U = TauCeti.Wkp.firstOrder 1 U := rfl

attribute [local irreducible] ordinaryPrincipalL supportedDriftL nativeCoefficientMassL
  nativeH2ThreeTermForcingL nativeH2FirstOrderL

/- Original raw nativeSupportedMassStrongL body, source614d..., retained verbatim.
This body never elaborated in receipts db9b9493... and f7c07d94... .
The typed assembly below is the same literal composition; exact constructor and
original concrete apply/evaluation identities are public proof roots.
  (ordinaryPrincipalL hcalc 0 F +
    (supportedDriftL hcalc 0 beta hbeta K hK hz).comp
      (TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 1)) +
    (nativeCoefficientMassL hcalc M).comp
      (TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 1)
-/

def nativeSupportedMassStrongL (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x, x ∉ K → beta x = 0) (M : SmoothCoefficientJets 1) :
    BallSobolev 2 →L[ℝ] BallSobolev 0 := by
  have hp := ordinaryPrincipalL hcalc 0 F
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hp
  have hd := supportedDriftL hcalc 0 beta hbeta K hK hz
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hd
  have hm := nativeCoefficientMassL hcalc M
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hm
  exact nativeH2ThreeTermForcingL hp hd hm nativeH2FirstOrderL

lemma nativeSupportedMassStrongL_apply (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x, x ∉ K → beta x = 0) (M : SmoothCoefficientJets 1) (U : BallSobolev 2) :
    nativeSupportedMassStrongL hcalc F beta hbeta K hK hz M U =
      ordinaryPrincipalL hcalc 0 F U +
        supportedDriftL hcalc 0 beta hbeta K hK hz (TauCeti.Wkp.firstOrder 1 U) +
        nativeCoefficientMassL hcalc M (TauCeti.Wkp.firstOrder 1 U) := by
  unfold nativeSupportedMassStrongL nativeH2ThreeTermForcingL nativeH2FirstOrderL
  rfl

lemma dirichletForcing_three_sum_eval (p d m : BallSobolev 0) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) (p+d+m) v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) p v +
        (TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) d v +
          TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) m v) := by
  simp only [TauCeti.PDE.dirichletForcing_apply,inner_add_left]
  ring

lemma ordinaryPrincipalL_zero_forcing_energy (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 2) (U : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (ordinaryPrincipalL hcalc 0 F U) v =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 F) 0 0 (TauCeti.Wkp.firstOrder 1 U) (v : BallH1) := by
  simpa only [TauCeti.Wkp.value_zero] using ordinaryPrincipalL_energy hcalc 0 F U v

lemma nativeSupportedMassStrongL_energy (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x, x ∉ K → beta x = 0) (M : SmoothCoefficientJets 1)
    (U : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (nativeSupportedMassStrongL hcalc F beta hbeta K hK hz M U) v =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 F) beta (coefficientValue 1 M)
      (TauCeti.Wkp.firstOrder 1 U) (v : BallH1) := by
  let u : BallH1 := TauCeti.Wkp.firstOrder 1 U
  let d : BallSobolev 0 := supportedDriftL hcalc 0 beta hbeta K hK hz u
  let m : BallSobolev 0 := nativeCoefficientMassL hcalc M u
  let p : BallSobolev 0 := ordinaryPrincipalL hcalc 0 F U
  have hFull := energyFormH1_eq_principal_add_nativeLowerForcing
    (coefficientMatrixField 2 F) beta (coefficientValue 1 M)
    (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) u v d m
    (supportedDriftL_zero_value_ae hcalc beta hbeta K hK hz u)
    (nativeCoefficientMassL_value_ae hcalc M u)
  have hP := ordinaryPrincipalL_zero_forcing_energy hcalc F U v
  have hSum := dirichletForcing_three_sum_eval p d m v
  have hPoint := congrArg
    (fun f : BallSobolev 0 => TauCeti.PDE.dirichletForcing
      (mu := (volume : Measure R3)) (Omega := ballOpens) f v)
    (nativeSupportedMassStrongL_apply hcalc F beta hbeta K hK hz M U)
  have hAdd := congrArg (fun t : ℝ => t+
    (TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) d v +
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) m v)) hP
  exact hPoint.trans (hSum.trans (hAdd.trans hFull.symm))

def nativeSupportedAdjointStrongL (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2)
    (C : SmoothCoefficientJets 1) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x, x ∉ K → beta x = 0) :
    BallSobolev 2 →L[ℝ] BallSobolev 0 :=
  nativeSupportedMassStrongL hcalc (nativePrincipalTransposeJets F) (-beta) hbeta.neg K hK
    (nativeSupportedNegativeDrift_zeroOutside beta K hz)
    (nativeSupportedAdjointMassCoefficient C beta hbeta K hK hz)

lemma nativeSupportedAdjointStrongL_energy (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2)
    (C : SmoothCoefficientJets 1) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x, x ∉ K → beta x = 0)
    (U : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (nativeSupportedAdjointStrongL hcalc F C beta hbeta K hK hz U) v =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (coefficientMatrixField 2 F x)ᵀ) (-beta)
      (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
      (TauCeti.Wkp.firstOrder 1 U) (v : BallH1) := by
  have he := nativeSupportedMassStrongL_energy hcalc (nativePrincipalTransposeJets F) (-beta)
    hbeta.neg K hK (nativeSupportedNegativeDrift_zeroOutside beta K hz)
    (nativeSupportedAdjointMassCoefficient C beta hbeta K hK hz) U v
  simpa only [nativeSupportedAdjointStrongL,coefficientMatrixField_nativePrincipalTransposeJets,
    coefficientValue_nativeSupportedAdjointMassCoefficient] using he

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativePrincipalTransposeJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientMatrixField_nativePrincipalTransposeJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedMassStrongL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedMassStrongL_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.dirichletForcing_three_sum_eval
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ordinaryPrincipalL_zero_forcing_energy
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedMassStrongL_energy
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedAdjointStrongL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedAdjointStrongL_energy

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH2ThreeTermForcingL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH2ThreeTermForcingL_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH2FirstOrderL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH2FirstOrderL_apply

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH2ThreeTermForcingL_eq_raw
