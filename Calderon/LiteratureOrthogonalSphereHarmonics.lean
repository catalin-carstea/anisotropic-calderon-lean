import Calderon.LiteratureSphereIntegrals

/-! Task 01 (see 01-orthogonality.md). Proof via Gaussian integrals: harmonic homogeneous
polynomials of different degrees are orthogonal for `e^{-|x|²} dx` (Gaussian integration by parts,
`gaussPair_eq_zero`), and in polar coordinates this Gaussian integral is a positive multiple of the
sphere integral. -/
namespace OAI.AnisotropicCalderon.SphereHarmonic
open AngularPolynomial

theorem orthogonalSphereHarmonics : OrthogonalSphereHarmonics := by
  intro k m hkm u hu v hv
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hu
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hv
  have hG := gaussPair_eq_sphere hp.1 hq.1
  rw [gaussPair_eq_zero hkm hp hq] at hG
  have hΓ : 0 < Real.Gamma ((((k + m : ℕ) : ℝ) + 3) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hI : ∫ ω : UnitSphere, pq p q ω ∂surfaceMeasure = 0 := by
    rcases mul_eq_zero.mp hG.symm with h | h
    · exact h
    · linarith [div_pos hΓ two_pos]
  rw [sphereInner_eq, hI, mul_zero]

end OAI.AnisotropicCalderon.SphereHarmonic
