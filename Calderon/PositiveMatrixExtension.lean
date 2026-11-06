import Calderon.NormalizedMetricMatrix
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MetricOperator
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def extensionParameterBump (p0 : P) (δ : ℝ) (hδ : 0 < δ) : ContDiffBump p0 :=
  ⟨δ/4,δ/2,by positivity,by linarith⟩

def extensionSpatialBump (R : ℝ) (hR : 1 < R) : ContDiffBump (0 : R3) :=
  ⟨1,R,by norm_num,hR⟩

def positiveExtensionWeight (p0 : P) (δ R : ℝ) (hδ : 0 < δ) (hR : 1 < R)
    (p : P × R3) : ℝ :=
  extensionParameterBump p0 δ hδ p.1 * extensionSpatialBump R hR p.2

def positiveMatrixExtension (G : P × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (G0 : Matrix (Fin 3) (Fin 3) ℝ) (p0 : P) (δ R : ℝ)
    (hδ : 0 < δ) (hR : 1 < R) (p : P × R3) : Matrix (Fin 3) (Fin 3) ℝ :=
  positiveExtensionWeight p0 δ R hδ hR p • G p +
    (1-positiveExtensionWeight p0 δ R hδ hR p) • G0

theorem positiveExtensionWeight_mem_Icc (p0 : P) (δ R : ℝ) (hδ : 0 < δ) (hR : 1 < R)
    (p : P × R3) : positiveExtensionWeight p0 δ R hδ hR p ∈ Icc (0 : ℝ) 1 := by
  have ha := (extensionParameterBump p0 δ hδ).nonneg' p.1
  have hb := (extensionSpatialBump R hR).nonneg' p.2
  have hc := (extensionParameterBump p0 δ hδ).le_one (x := p.1)
  have hd := (extensionSpatialBump R hR).le_one (x := p.2)
  constructor
  · exact mul_nonneg ha hb
  · change extensionParameterBump p0 δ hδ p.1 * extensionSpatialBump R hR p.2 ≤ 1
    nlinarith

theorem contDiff_positiveExtensionWeight (p0 : P) (δ R : ℝ)
    (hδ : 0 < δ) (hR : 1 < R) :
    ContDiff ℝ ∞ (positiveExtensionWeight p0 δ R hδ hR) :=
  ((extensionParameterBump p0 δ hδ).contDiff.comp contDiff_fst).mul
    ((extensionSpatialBump R hR).contDiff.comp contDiff_snd)

theorem contDiff_positiveMatrixExtension (G : P × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hG : ContDiff ℝ ∞ G) (G0 : Matrix (Fin 3) (Fin 3) ℝ) (p0 : P) (δ R : ℝ)
    (hδ : 0 < δ) (hR : 1 < R) :
    ContDiff ℝ ∞ (positiveMatrixExtension G G0 p0 δ R hδ hR) := by
  have hα := contDiff_positiveExtensionWeight p0 δ R hδ hR
  exact (hα.smul hG).add ((contDiff_const.sub hα).smul contDiff_const)

theorem positiveMatrixExtension_eq_of_weight_zero
    (G : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (G0 : Matrix (Fin 3) (Fin 3) ℝ)
    (p0 : P) (δ R : ℝ) (hδ : 0 < δ) (hR : 1 < R) (p : P × R3)
    (hz : positiveExtensionWeight p0 δ R hδ hR p = 0) :
    positiveMatrixExtension G G0 p0 δ R hδ hR p = G0 := by
  simp [positiveMatrixExtension,hz]

theorem positiveMatrixExtension_eq_on_inner
    (G : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (G0 : Matrix (Fin 3) (Fin 3) ℝ)
    (p0 : P) (δ R : ℝ) (hδ : 0 < δ) (hR : 1 < R) (p : P × R3)
    (hp : dist p.1 p0 ≤ δ/4) (hz : ‖p.2‖ ≤ 1) :
    positiveMatrixExtension G G0 p0 δ R hδ hR p = G p := by
  have hb : extensionParameterBump p0 δ hδ p.1 = 1 :=
    (extensionParameterBump p0 δ hδ).one_of_mem_closedBall hp
  have hs : extensionSpatialBump R hR p.2 = 1 := by
    apply (extensionSpatialBump R hR).one_of_mem_closedBall
    simpa only [extensionSpatialBump,mem_closedBall,dist_zero_right] using hz
  simp [positiveMatrixExtension,positiveExtensionWeight,hb,hs]

theorem positiveMatrixExtension_posDef
    (G : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (G0 : Matrix (Fin 3) (Fin 3) ℝ)
    (hG0 : G0.PosDef) (p0 : P) (δ R : ℝ) (hδ : 0 < δ) (hR : 1 < R)
    (hpos : ∀ p : P × R3, dist p.1 p0 ≤ δ → ‖p.2‖ ≤ R → (G p).PosDef)
    (p : P × R3) : (positiveMatrixExtension G G0 p0 δ R hδ hR p).PosDef := by
  by_cases hz : positiveExtensionWeight p0 δ R hδ hR p = 0
  · rw [positiveMatrixExtension_eq_of_weight_zero G G0 p0 δ R hδ hR p hz]
    exact hG0
  have hα := positiveExtensionWeight_mem_Icc p0 δ R hδ hR p
  have hαpos : 0 < positiveExtensionWeight p0 δ R hδ hR p :=
    lt_of_le_of_ne hα.1 (Ne.symm hz)
  have hne := mul_ne_zero_iff.mp hz
  have hp : dist p.1 p0 < δ/2 := by
    have hm : p.1 ∈ Function.support (extensionParameterBump p0 δ hδ) := hne.1
    simpa only [ContDiffBump.support_eq,extensionParameterBump,mem_ball] using hm
  have hs : ‖p.2‖ < R := by
    have hm : p.2 ∈ Function.support (extensionSpatialBump R hR) := hne.2
    simpa only [ContDiffBump.support_eq,extensionSpatialBump,mem_ball,dist_zero_right] using hm
  have hGP := hpos p (hp.le.trans (by linarith)) hs.le
  exact (hGP.smul hαpos).add_posSemidef (hG0.posSemidef.smul (sub_nonneg.mpr hα.2))

theorem positiveMatrixExtension_eq_outside_spatial
    (G : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (G0 : Matrix (Fin 3) (Fin 3) ℝ)
    (p0 : P) (δ R : ℝ) (hδ : 0 < δ) (hR : 1 < R) (p : P × R3)
    (hz : R ≤ ‖p.2‖) : positiveMatrixExtension G G0 p0 δ R hδ hR p = G0 := by
  apply positiveMatrixExtension_eq_of_weight_zero
  have hs : extensionSpatialBump R hR p.2 = 0 := by
    apply (extensionSpatialBump R hR).zero_of_le_dist
    simpa only [extensionSpatialBump,dist_zero_right] using hz
  simp [positiveExtensionWeight,hs]
end OAI.AnisotropicCalderon.MetricOperator
