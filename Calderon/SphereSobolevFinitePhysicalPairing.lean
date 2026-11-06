import Calderon.SphereSobolevFinitePhysicalTestPairing
import Calderon.SphereSobolevFinitePhysicalPacketConstructorDiagnostic

set_option autoImplicit false
noncomputable section
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
attribute [local irreducible] sphereSobolevSingleL sphereSobolevCoefficientL sphereSobolevZeroEquiv

lemma inner_zeroEquiv_symm_clm_finite_packets
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (T : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (s t : Finset ℕ) (u v : ∀ k, harmonicSphereSubspace k) :
    ⟪(sphereSobolevZeroEquiv hO hD).symm
      (T (∑ n ∈ s, sphereSobolevSingleL 1 n (u n))),
      (∑ m ∈ t, (v m : SphereL2))⟫_ℝ =
    ∑ m ∈ t, ∑ n ∈ s,
      ⟪sphereSobolevCoefficientL 0 m (T (sphereSobolevSingleL 1 n (u n))),v m⟫_ℝ := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PHYSICAL_PACKET_PROOF_ENTER"
    out.flush
  have hPhysical :
      ⟪(sphereSobolevZeroEquiv hO hD).symm
        (T (∑ n ∈ s, sphereSobolevSingleL 1 n (u n))),
        (∑ m ∈ t, (v m : SphereL2))⟫_ℝ =
      ∑ m ∈ t, ⟪sphereSobolevCoefficientL 0 m
        (T (∑ n ∈ s, sphereSobolevSingleL 1 n (u n))),v m⟫_ℝ :=
    inner_zeroEquiv_symm_finite_harmonic_test hO hD
      (T (∑ n ∈ s, sphereSobolevSingleL 1 n (u n))) t v
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PHYSICAL_PACKET_TEST_DECODED"
    out.flush
  apply hPhysical.trans
  apply Finset.sum_congr rfl
  intro m _
  have hMap : sphereSobolevCoefficientL 0 m
      (T (∑ n ∈ s, sphereSobolevSingleL 1 n (u n))) =
      ∑ n ∈ s, sphereSobolevCoefficientL 0 m (T (sphereSobolevSingleL 1 n (u n))) :=
    (congrArg (sphereSobolevCoefficientL 0 m)
      (sphereSobolev_clm_finite_packet_apply_diagnostic T s u)).trans
        (map_sum (sphereSobolevCoefficientL 0 m)
          (fun n => T (sphereSobolevSingleL 1 n (u n))) s)
  rw [hMap, sum_inner]

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.inner_zeroEquiv_symm_clm_finite_packets
end OAI.AnisotropicCalderon.SphereHarmonic
