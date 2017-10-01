# quantitative analysis

 https://en.wikipedia.org/wiki/Quantitative_analyst
 http://economics.sas.upenn.edu/~jesusfv/comparison_languages.pdf A Comparison of Programming Languages in Economics

black_scholes s:R x:R t:R r:R σ:R : R = 
  d0 = R.log s/x + (r + σ²/2.)*t
  d1 = d0 / σ√t
  d2 = d1 - σ√t
  s ϕ d1 - (x * R.ℯ^(-r * t)) ϕ d2
Fact (black_scholes 71.95 72. 0.002968 0.0025 0.37 ≈ 0.554387)
