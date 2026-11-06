import Calderon.ActualLowerUSAdjointZeroPolynomial
import Calderon.ActualFiniteHarmonicModelQuadraticAngularAdjoint
import Calderon.ActualPerturbedModelSupport

/-!
Author: GPT-6.1 Sol, author support only.
Before-code: ../lower-r-z-upfront.md.
Actual finite-core angular adjoint of the complete original J, for weak tests.
No analytic premise or lower-only adjoint-closure assertion is introduced.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (hF : SphereFischerInner)

private lemma lowerGenerator_original_expansion
    (i : LowerCoreAngularGeneratorIndex) (x : R3) :
    HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
      (lowerCoreAngularGenerator hO hD hF i) x 1 := by
  rcases i with u | ((bc | u) | a)
  · cases u
    exact hasCoreScalarExpansionBound_identity hO hD hF x
  · exact hasCoreScalarExpansionBound_neg hO hD _ _ x 1
      (hasCoreScalarExpansionBound_generator hO hD hF (Sum.inr (Sum.inr (Sum.inl bc))) x)
  · cases u
    exact hasCoreScalarExpansionBound_generator hO hD hF (Sum.inr (Sum.inr (Sum.inr true))) x
  · exact hasCoreScalarExpansionBound_generator hO hD hF (Sum.inl a) x

private lemma lowerQuadratic_original_expansion
    (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (x : R3) (C : ℝ)
    (hA : HasCoreScalarExpansionBound hO hD
      (fun ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex =>
        lowerCoreAngularGenerator hO hD hF (Prod.fst ij) *
          lowerCoreAngularGenerator hO hD hF (Prod.snd ij)) A x C) :
    HasCoreScalarExpansionBound hO hD
      (fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
        coreAngularGenerator hO hD hF (Prod.fst ij) * coreAngularGenerator hO hD hF (Prod.snd ij)) A x C := by
  obtain ⟨c,hc,he,hm⟩ := hA
  rw [he]
  apply hasCoreScalarExpansionBound_mono hO hD _ _ x _ C _ hm
  unfold coreScalarCombination
  apply hasCoreScalarExpansionBound_sum hO hD
  intro ij _
  have hp : HasCoreScalarExpansionBound hO hD
      (fun kl : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
        coreAngularGenerator hO hD hF (Prod.fst kl) * coreAngularGenerator hO hD hF (Prod.snd kl))
      (lowerCoreAngularGenerator hO hD hF (Prod.fst ij) *
        lowerCoreAngularGenerator hO hD hF (Prod.snd ij)) x 1 := by
    simpa only [one_mul] using hasCoreScalarExpansionBound_product hO hD
      (coreAngularGenerator hO hD hF) (coreAngularGenerator hO hD hF)
      (scalarCentral_coreAngularGenerator hO hD hF) _ _ x 1 1
      (lowerGenerator_original_expansion hO hD hF (Prod.fst ij) x)
      (lowerGenerator_original_expansion hO hD hF (Prod.snd ij) x)
  simpa only [mul_one] using hasCoreScalarExpansionBound_scalar_mul hO hD _ _ x 1 hp (c ij) (hc ij)

variable (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
  (hg2 : IsAdmissibleMetric g2) (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)

/-- The actual globally pointwise angular adjoint is produced from the exact
original smooth quadratic dictionary, with no norm callback. -/
theorem exists_nativeULowerAdjointZero_sphere_adjoint :
    ∃ Jstar : Module.End ℝ (smoothCompactFiniteSphereCore hO hD),
      ∀ F G : smoothCompactFiniteSphereCore hO hD, ∀ x : R3,
        ⟪(nativeULowerAdjointZeroCoefficient hO hD hF g g2 hg hg2
          L q dr Ar p hdr hAr F).val x,G.val x⟫_ℝ = ⟪F.val x,(Jstar G).val x⟫_ℝ := by
  have hA := lowerQuadratic_original_expansion hO hD hF _ (0 : R3) _
    (hasCoreScalarExpansionBound_nativeULowerAdjointZero_lower hO hD hF g g2 hg hg2
      L q dr Ar p hdr hAr (0 : R3))
  obtain ⟨Jstar,hAdj,_hMass⟩ := exists_pointwise_adjoint_of_quadratic_expansion hO hD hF
    (nativeULowerAdjointZeroCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr)
    (0 : R3) _ hA
  exact ⟨Jstar,hAdj⟩

/-- A genuine finite-core sphere adjoint of J. Raising on the finite test is allowed. -/
def nativeULowerAdjointZeroSphereAdjointCore :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  Classical.choose (exists_nativeULowerAdjointZero_sphere_adjoint hO hD hF g g2 hg hg2
    L q dr Ar p hdr hAr)

/-- Global pointwise adjunction, independent of the base point used to select its witness. -/
theorem nativeULowerAdjointZeroSphereAdjointCore_inner
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪(nativeULowerAdjointZeroCoefficient hO hD hF g g2 hg hg2
        L q dr Ar p hdr hAr F).val x,G.val x⟫_ℝ =
    ⟪F.val x,(nativeULowerAdjointZeroSphereAdjointCore hO hD hF g g2 hg hg2
        L q dr Ar p hdr hAr G).val x⟫_ℝ :=
  Classical.choose_spec (exists_nativeULowerAdjointZero_sphere_adjoint hO hD hF g g2 hg hg2
    L q dr Ar p hdr hAr) F G x

/-- The chosen true angular adjoint preserves the original finite input support. -/
theorem finiteCoreSupportPreserving_nativeULowerAdjointZeroSphereAdjointCore :
    FiniteCoreSupportPreserving hO hD
      (nativeULowerAdjointZeroSphereAdjointCore hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr) := by
  intro F
  apply closure_mono
  intro x hx hz
  apply hx
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  have hh := nativeULowerAdjointZeroSphereAdjointCore_inner hO hD hF g g2 hg hg2
    L q dr Ar p hdr hAr
    (nativeULowerAdjointZeroSphereAdjointCore hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F) F x
  rw [hz,inner_zero_right] at hh
  exact hh.symm

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
