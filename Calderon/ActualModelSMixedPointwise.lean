import Calderon.ActualPrincipalLeadingScalarSReference
import Calderon.ActualCofinalModelSignedComparison

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualModelSMixedComparison
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints

/-- Exact real physical norm expansion, with no operator or adjoint assumptions. -/
theorem signed_norm_add_expansion (a b s sd : SphereL2) :
    ‖a+s‖^2-‖b+sd‖^2 =
      (‖a‖^2-‖b‖^2)+(‖s‖^2-‖sd‖^2)+2*(⟪a,s⟫_ℝ-⟪b,sd⟫_ℝ) := by
  simp only [norm_add_sq_real]
  ring

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

local notation "MR" => nativeModelRaising hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr
local notation "MD" => nativeModelAdjoint hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr
local notation "ZZ" => nativeZ hO hD hF g hg L q dr Ar p hdr hAr
local notation "SO" => ActualHigherSFormation.nativeHigherSOut
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
  dr Ar p hdr hAr q hreg data.δ0 data.germs g2
local notation "SD" => ActualHigherSAdjointFormation.higherSAdjointOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  hreg data.δ0 data.germs g2 dr Ar p hdr hAr q

/-- Original shifted model plus actual S: exact T/S and U/S split.
The literal S-self norm defect remains untouched for Main's reserved estimate. -/
theorem actual_model_S_signed_pointwise (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    let m := (MR F).val x
    let md := (MD F).val x
    let z := (ZZ F).val x
    let s := SO F x
    let sd := SD F x
    let t := nativeTField hO hD hF g hg L q dr Ar p F x
    let td := nativeTdagField hO hD hF g hg L q dr Ar p F x
    let u := nativeUField hO hD hF g g2 hg L q dr Ar p F x
    let ud := nativeUdagField hO hD hF g g2 hg L q dr Ar p F x
    ‖m+s‖^2-‖(md+(2:ℝ) • z)+sd‖^2 =
      (‖m‖^2-‖md+(2:ℝ) • z‖^2)+(‖s‖^2-‖sd‖^2)+
        4*(⟪t,s⟫_ℝ-⟪td+z,sd⟫_ℝ)+2*(⟪u,s⟫_ℝ-⟪ud,sd⟫_ℝ) := by
  dsimp only
  have hm : (MR F).val x =
      nativeTField hO hD hF g hg L q dr Ar p F x+
      nativeTField hO hD hF g hg L q dr Ar p F x+
      nativeUField hO hD hF g g2 hg L q dr Ar p F x := by
    simp only [nativeModelRaising,two_mul,LinearMap.add_apply,Submodule.coe_add,Pi.add_apply]
    rfl
  have hmd : (MD F).val x =
      nativeTdagField hO hD hF g hg L q dr Ar p F x+
      nativeTdagField hO hD hF g hg L q dr Ar p F x+
      nativeUdagField hO hD hF g g2 hg L q dr Ar p F x := by
    simp only [nativeModelAdjoint,two_mul,LinearMap.add_apply,Submodule.coe_add,Pi.add_apply]
    rfl
  have hc :
      ⟪(MR F).val x,SO F x⟫_ℝ-⟪(MD F).val x+(2:ℝ) • (ZZ F).val x,SD F x⟫_ℝ =
        2*(⟪nativeTField hO hD hF g hg L q dr Ar p F x,SO F x⟫_ℝ-
          ⟪nativeTdagField hO hD hF g hg L q dr Ar p F x+(ZZ F).val x,SD F x⟫_ℝ)+
        (⟪nativeUField hO hD hF g g2 hg L q dr Ar p F x,SO F x⟫_ℝ-
          ⟪nativeUdagField hO hD hF g g2 hg L q dr Ar p F x,SD F x⟫_ℝ) := by
    rw [hm,hmd]
    simp only [inner_add_left,real_inner_smul_left]
    ring
  calc
    _ = ((‖(MR F).val x‖^2-‖(MD F).val x+(2:ℝ) • (ZZ F).val x‖^2)+
        (‖SO F x‖^2-‖SD F x‖^2))+
        2*(⟪(MR F).val x,SO F x⟫_ℝ-
          ⟪(MD F).val x+(2:ℝ) • (ZZ F).val x,SD F x⟫_ℝ) :=
      signed_norm_add_expansion _ _ _ _
    _ = _ := by rw [hc]; ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualModelSMixedComparison
