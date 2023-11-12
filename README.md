# ForML

This project aims to prove useful theorems for machine learning in Lean.

## Definitions

* Smooth, compact bump functions (with topology)

## Theorems

* Schwartz functions
  * Integral of a Schwartz function as a `ContinuousLinearMap`
  * Integral against `HasTemperateGrowth` function is a tempered distribution
  * `HasTemperateGrowth` for trigonometric functions
  * Application of a CLM commutes with (iterated) Fréchet derivative
  * Iterated partial derivative is equal to iterated Fréchet derivative
* Gaussian tends to Dirac delta
* Second mean value theorem for (improper) integrals
* Hölder's inequality for functions in L1 and L∞

## Todo

* Fourier transform of Schwartz function
* Fourier transform of tempered distribution
* Schwartz function: Integral up to a point as a CLM

## Roadmap (depth first)

* Sum of two independent r.v.s is convolution of pdfs (where pdf is a distribution)
  * Define Fourier transform for distributions
    * Define distribution as continuous linear map on test functions
  * Fourier transform of convolution of distributions
    * Fourier transform of Dirac delta, constant, sin/cos, derivative, integral, ...

## Other todos

* Generate docs (and add links to readme)
* Add CI
