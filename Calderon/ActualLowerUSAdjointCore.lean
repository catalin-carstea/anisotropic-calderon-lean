import Calderon.ActualLowerUSAdjointCoefficients
import Calderon.ActualPerturbedModelSupport

/-!
Author: gpt-6.1-sol, lower U/S authoring support.
Before-code expansion: ../adjoint-core-expansion-v001.md.
This is a finite-core domain bridge, with no quantitative analytic assertion.
Root owns diagnostics and the complete native check; no author compilation.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace

namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  ActualScalarPrincipalAdjoint ReferenceDensityBounds NormalizedPrincipalMetric
  PrincipalCommutator ConformalDepth

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (hF : SphereFischerInner) (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
  (hg2 : IsAdmissibleMetric g2) (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)

local notation "FC" => smoothCompactFiniteSphereCore hO hD
local notation "D1" => nativeULowerAdjointFirstCoefficient hO hD hF g g2 hg hg2
  L q dr Ar p hdr hAr
local notation "D0" => nativeULowerAdjointZeroCoefficient hO hD hF g g2 hg hg2
  L q dr Ar p hdr hAr

/-- The exact original adjoint lower coefficients act only on the finite core. -/
def nativeULowerAdjointCore : Module.End ℝ FC :=
  ActualModelCommutatorWords.modelFirstOrder
    (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) D1 D0

/-- Evaluation agrees with the existing literal lower adjoint output. -/
theorem nativeULowerAdjointCore_apply (F : FC) (x : R3) :
    (nativeULowerAdjointCore hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F).val x =
      nativeUAdjointFirstZeroOut hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F x := by
  simpa only [nativeULowerAdjointCore, ActualModelCommutatorWords.modelFirstOrder,
    LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply,
    Submodule.coe_add, Submodule.coe_sum, Pi.add_apply, Finset.sum_apply] using
    (nativeUAdjointFirstZeroOut_eq_lower_adjoint_coefficients
      hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F x).symm

/-- Locality uses the original B,V and exact scalar density correction. -/
theorem finiteCoreSupportPreserving_nativeULowerAdjointFirstCoefficient (i : Fin 3) :
    FiniteCoreSupportPreserving hO hD (D1 i) := by
  unfold nativeULowerAdjointFirstCoefficient
  apply finiteCoreSupportPreserving_sub hO hD
  · apply finiteCoreSupportPreserving_add hO hD
    · exact finiteCoreSupportPreserving_nativeB hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr i
    · exact finiteCoreSupportPreserving_nativeV hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr i
  · exact finiteCoreSupportPreserving_coreScalar hO hD _ _

/-- The checked C+W-a0 dictionary retains every original zero-order term. -/
theorem finiteCoreSupportPreserving_nativeULowerAdjointZeroCoefficient :
    FiniteCoreSupportPreserving hO hD D0 := by
  rw [nativeULowerAdjointZeroCoefficient_eq_original hO hD hF g g2 hg hg2
    L q dr Ar p hdr hAr]
  apply finiteCoreSupportPreserving_sub hO hD
  · apply finiteCoreSupportPreserving_add hO hD
    · exact finiteCoreSupportPreserving_nativeC hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
    · exact finiteCoreSupportPreserving_nativeW hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
  · exact finiteCoreSupportPreserving_coreScalar hO hD _ _

/-- No extra support or finite-output hypothesis is needed for the lower input. -/
theorem finiteCoreSupportPreserving_nativeULowerAdjointCore :
    FiniteCoreSupportPreserving hO hD
      (nativeULowerAdjointCore hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr) := by
  unfold nativeULowerAdjointCore
  exact finiteCoreSupportPreserving_modelFirstOrder hO hD _ _ _
    (fun i => finiteCoreSupportPreserving_coreDirectionalDerivative hO hD _)
    (fun i => finiteCoreSupportPreserving_nativeULowerAdjointFirstCoefficient
      hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr i)
    (finiteCoreSupportPreserving_nativeULowerAdjointZeroCoefficient
      hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSAdjointCore
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualModelSMixedComparison ActualAngularHighDraft ConformalDepth
  ReferenceWeightedApproximation ReferenceDensityBounds NormalizedPrincipalMetric

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
  (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
  (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)

local notation "LA" => nativeULowerAdjointCore hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
local notation "LO" => nativeUAdjointFirstZeroOut hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
local notation "SO" => ActualHigherSFormation.nativeHigherSOut
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
  dr Ar p hdr hAr q hreg data.δ0 data.germs g2
local notation "SD" => ActualHigherSAdjointFormation.higherSAdjointOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  hreg data.δ0 data.germs g2 dr Ar p hdr hAr q
local notation "CRoom" δ:max => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs δ
local notation "Tq" => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)

/-- Specialize the existing full physical adjunction to two genuine finite inputs. -/
theorem actual_lower_adjoint_S_weak_identity_of_common_room
    (δ : ℝ) (Cm : CRoom δ) (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, Tq x ∈ ParamRoom δ) :
    Integrable (fun x => referenceDensityFamily g L (q,x) * ⟪LO F x, SD F x⟫_ℝ) ∧
    Integrable (fun x => referenceDensityFamily g L (q,x) * ⟪F.val x, SO (LA F) x⟫_ℝ) ∧
    (∫ x, referenceDensityFamily g L (q,x) * ⟪LO F x, SD F x⟫_ℝ) =
      ∫ x, referenceDensityFamily g L (q,x) * ⟪F.val x, SO (LA F) x⟫_ℝ := by
  have hTLA : ∀ x ∈ tsupport (LA F).val, Tq x ∈ ParamRoom δ := by
    intro x hx
    exact hTF x (finiteCoreSupportPreserving_nativeULowerAdjointCore
      hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F hx)
  have hWeak := ActualHigherSAdjointFormation.integrated_higherS_physical_adjoint
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs δ Cm g2 hg2 dr Ar p hdr hAr q F (LA F) hTF hTLA
  have hLower : Integrable
      (fun x => referenceDensityFamily g L (q,x) * ⟪LO F x, SD F x⟫_ℝ) :=
    hWeak.2.1.congr (Filter.Eventually.of_forall (fun x => by
      dsimp only
      have hv : (LA F).val x = LO F x :=
        nativeULowerAdjointCore_apply hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F x
      change referenceDensityFamily g L (q,x) * ⟪SD F x, (LA F).val x⟫_ℝ =
        referenceDensityFamily g L (q,x) * ⟪LO F x, SD F x⟫_ℝ
      rw [hv, real_inner_comm]))
  refine ⟨hLower,hWeak.1,?_⟩
  calc
    _ = ∫ x, referenceDensityFamily g L (q,x) * ⟪SD F x, (LA F).val x⟫_ℝ :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x => by
        dsimp only
        have hv : (LA F).val x = LO F x :=
          nativeULowerAdjointCore_apply hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F x
        change referenceDensityFamily g L (q,x) * ⟪LO F x, SD F x⟫_ℝ =
          referenceDensityFamily g L (q,x) * ⟪SD F x, (LA F).val x⟫_ℝ
        rw [hv, real_inner_comm]))
    _ = _ := hWeak.2.2.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSAdjointCore
