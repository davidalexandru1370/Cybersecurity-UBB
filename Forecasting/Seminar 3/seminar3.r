library(fpp3)
library(tidyverse)


# a) Transform the data into a tsibble. (The file contains just a sequence of numbers, to transform it
# into a tsibble, you need an index column. First you need to transform it into a tibble, then you can
# artificially create a sequence of years, with seq(1901, 1999) and add this as a column – use mutate
# – and finally transform it into a tsibble)

earthquakes_data <- read_csv("../Desktop/folders/Cybersecurity-UBB/Forecasting/Seminar 3/Earthquake.csv", col_names = TRUE)
n_rows <- nrow(earthquakes_data)

earthquakes_data |>
    as_tibble() |>
    mutate(Year = seq(1901, 1901 + n_rows - 1)) |>
    as_tsibble(index = Year) -> earthquakes

print(earthquakes)

# b)  Autoplot the data

autoplot(earthquakes) + labs(title = "Earthquakes", x = "Year", y = "Number of Earthquakes")


# According to what you see on the plot, do you think the data has a trend or does it seem to be
# stationary?

# The data has a trend, as the number of earthquakes increases over time.

# d) Plot the autocorrelation of the data for at least 16 lags. What do the autocorrelations tell you
# about the data? Is it stationary?

earthquakes |>
    ACF(lag_max = 16) |>
    autoplot() + labs(title = "Autocorrelation of Earthquakes", x = "Lag", y = "Autocorrelation")

# The autocorrelation plot shows that the data is not stationary, as the autocorrelations are not
# constant over time.


# e) Use the KPSS test to check if the data is stationary.

earthquakes |>
    features(EarthQuake, unitroot_kpss) |>
    print()


# Let's interpret these KPSS test results:
# 1. Test Statistic (kpss_stat) = 0.349
# This is the calculated test statistic from your data
# Compare this with critical values:
# 10% level: 0.347
# 5% level: 0.463
# 1% level: 0.739
# Your value (0.349) is just slightly above the 10% critical value
# P-value (kpss_pvalue) = 0.0990
# This is greater than 0.05 (the common significance level)
# Therefore, we fail to reject the null hypothesis
# Remember: The null hypothesis is that the series is stationary
# Conclusion:
# Since p-value (0.0990) > 0.05, we don't have enough evidence to conclude that the series is non-stationary
# In other words, we can treat this time series as stationary at the 5% significance level
# However, note that it's close to being non-stationary at the 10% level (p-value < 0.10)
# This suggests that your earthquake data shows characteristics of a stationary series, which is good news for further time series analysis!

# f) Use the ADF test to check if the data is stationary. Do the two tests agree? If not, which one do
# you tend to agree with?
library(tseries)
adf.test(earthquakes$EarthQuake)
# 1. Test Statistic (Dickey-Fuller = -3.2364)
# More negative values suggest stationarity
# The more negative the value, the stronger the evidence for stationarity
# P-value = 0.08583
# This is > 0.05 but < 0.10
# At 5% significance level: Fail to reject the null hypothesis
# At 10% significance level: Reject the null hypothesis
# Important Note: The ADF test has opposite hypotheses from KPSS:
# Null hypothesis (H0): Series is non-stationary (has a unit root)
# Alternative hypothesis (H1): Series is stationary
# Conclusion:
# Since p-value (0.08583) > 0.05, we fail to reject the null hypothesis at the 5% level
# This suggests there is some evidence of non-stationarity, but it's not very strong
# The result is borderline, as it would be significant at the 10% level
# Comparing with your KPSS test:
# KPSS suggested stationarity (p = 0.0990)
# ADF suggests non-stationarity (p = 0.08583)
# Both tests give borderline results, indicating the series might have weak non-stationary characteristics
# This kind of conflicting/borderline result is common in practice and suggests the series might be near the boundary between stationary and non-stationary behavior.

# a) Using the unitroot_ndiffs and unitroot_nsdiff functions, check how many times the time series
# should be differenced to be stationary. If needed, difference the data and check again the
# autocorrelation

earthquakes |>
    features(EarthQuake, unitroot_ndiffs) |>
    print()


earthquakes |>
    features(EarthQuake, unitroot_nsdiffs) |>
    print()
  
# g) Use STL decomposition to decompose the data. What do you observe?
# h) A  decomposition  is  good  if  the  remainder  is  white  noise.  Get  the  remainder  from  the
# decomposition and plot its autocorrelations. Is it white noise?

earthquakes |>
    model(
        STL(EarthQuake ~ trend(window = 7) + season(period = "1 year"))
    ) |>
    components() |>
    autoplot()

