import Calderon.LiteratureSphereIntegrals

/-! Proof via Gaussian integrals: for harmonic homogeneous
`p, q` of degree `k`, `∫_{ℝ³} p q e^{-|x|²} = π^{3/2} 2^{-k} [p, q]` (Gaussian integration by
parts, `gaussPair_eq_fischer`), while polar coordinates give
`∫_{ℝ³} p q e^{-|x|²} = (∫_{S²} p q dσ) Γ(k + 3/2) / 2`; the degree-zero case fixes `σ(S²)`, and
`Γ(k + 3/2) / Γ(3/2) = 2^{-k} ∏_{j<k} (3 + 2j)`. -/
namespace OAI.AnisotropicCalderon.SphereHarmonic
open AngularPolynomial

theorem sphereFischerInner : SphereFischerInner := by
  intro k p q hp hq
  have hG := gaussPair_eq_sphere hp.1 hq.1
  rw [gaussPair_eq_fischer hp hq, gamma_half_odd] at hG
  have hσ := surface_mul_gamma
  have hΓ : 0 < Real.Gamma (3 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  have hN : 0 < sphereNormalization 3 k := Finset.prod_pos fun j _ => by positivity
  have hπ : 0 < Real.pi ^ ((3 : ℝ) / 2) := by positivity
  have hS : 0 < (surfaceMeasure Set.univ).toReal := by
    have := hσ ▸ hπ
    nlinarith [this]
  rw [sphereInner_eq, normalizedFischerInner, Fintype.card_fin]
  set I := ∫ ω : UnitSphere, pq p q ω ∂surfaceMeasure
  field_simp
  rw [← hσ] at hG
  field_simp at hG
  nlinarith [hG, hΓ, hS, hN]

end OAI.AnisotropicCalderon.SphereHarmonic
