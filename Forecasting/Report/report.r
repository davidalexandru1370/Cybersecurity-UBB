library(fpp3)        # For forecasting functions
library(tidyverse)   # For data manipulation
library(tsibble)     # For time series data structures
library(feasts)      # For time series features
library(fable)       # For forecasting models
library(lubridate)   # For date handling
library(prophet)     # For Prophet model
library(fable.prophet) # For Prophet integration with fable
library(tseries) # For adf test
library(TTR) # For EMA


folder_path <- "../Desktop/folders/Cybersecurity-UBB/Forecasting/Report"
electricity_data_df <- read_csv(paste0(folder_path, "/Electric_Production.csv"), col_names = TRUE)

electric_prod <- electricity_data_df |>
  mutate(
    Date = as.Date(DATE, format = "%m/%d/%Y"),
    Production = IPG2211A2N
  ) |>
  select(Date, Production) |>
  as_tsibble(index = Date)

electric_prod |>
  autoplot(Production, color = "blue") +
  scale_x_date(
    date_breaks = "5 years",           # Set breaks every 5 years
    date_labels = "%Y"                 # Show only year
  ) +
  labs(
    title = "Electric Production Index",
    x = "Year",
    y = "Production Index"
  ) +
  theme(
    axis.text.x = element_text(angle = 0)  # Make sure x-axis labels are readable
  )
#By looking at the above plot we can see, there is an upward trend over the period of time.
ggsave(paste0(folder_path, "/electric_prod.png"), width = 10, height = 6, dpi = 300)

ma_data <- electric_prod |>
  mutate(
    MA = slider::slide_dbl(Production, mean, .before = 6, .after = 5, .complete = TRUE),
    Detrended = Production - MA
  )

# Create plot with all three series
ma_data |>
  pivot_longer(cols = c(Production, MA, Detrended),
               names_to = "Series",
               values_to = "Value") |>
  ggplot(aes(x = Date, y = Value, color = Series)) +
  geom_line() +
  scale_color_manual(values = c("Production" = "blue", 
                                "MA" = "red", 
                                "Detrended" = "green")) +
  scale_x_date(date_breaks = "5 years",
               date_labels = "%Y") +
  labs(
    title = "Electric Production: Original, Moving Average, and Detrended",
    x = "Year",
    y = "Value",
    color = "Series"
  ) +
  theme_minimal() +
  theme(
    axis.text.x = element_text(angle = 0),
    legend.position = "bottom"
  )

# Save the plot
ggsave(paste0(folder_path, "/electric_prod_decomposition.png"), 
       width = 10, height = 6, dpi = 300)

summary(electric_prod$Production)

#The minimum production recorded is 55.32,
#while the maximum is 129.40, indicating a significant range of variability.
#The first quartile (77.11) and third quartile (100.52)
#show that 25% of values are below 77.11 and 75% are below 100.52, respectively.
#The median production level is 89.78, and the mean is 88.85, suggesting 
#a fairly symmetrical distribution.

# Decompose the time series
#electric_prod
#is_regular(electric_prod)
electric_prod
decomposed <- electric_prod |>
    mutate(Date = yearmonth(Date)) |>
    index_by(Date) |>
    summarise(Production = mean(Production)) |>
    select(Date, Production) |>
    model(stl = STL(Production)) |>
    components()

decomposed

# Create the combined plot
decomposed |>
  autoplot() +
  labs(
    title = "Decomposition of Electric Production Time Series",
    x = "Year"
  ) +
  theme(
    axis.text.x = element_text(angle = 0),
    legend.position = "none"
  )

# Save the plot
ggsave(paste0(folder_path, "/electric_prod_stl_decomposition.png"), 
       width = 10, height = 8, dpi = 300)


#Check for Stationarity
#Augmented Dickey-Fuller Test
#Null Hypothesis: Time Series is non-stationary.

electric_prod |>
  mutate(Date = yearmonth(Date)) |>
  index_by(Date) |>
  summarise(Production = mean(Production)) |>
  select(Date, Production) |>
  ACF(lag_max = 12) |>
  autoplot() + labs(title = "Autocorrelation of Electric production", x = "Lag", y = "Autocorrelation")

ggsave(paste0(folder_path, "/electric_prod_acf.png"), 
       width = 10, height = 6, dpi = 300)

# The autocorrelation plot shows that the data is not stationary, as the autocorrelations are not
# constant over time.


# e) Use the KPSS test to check if the data is stationary.

electric_prod |>
  mutate(Date = yearmonth(Date)) |>
  index_by(Date) |>
  summarise(Production = mean(Production)) |>
  select(Date, Production) |>
  features(Production, unitroot_kpss) |>
  print()

adf.test(electric_prod$Production, k=12)
#The p-value of 0.01 is less than the common significance level of 0.05.
#This indicates that we can reject the null hypothesis.
#This implies that the time series is non-stationary.

# First, let's try Box-Cox transformation
lambda <- electric_prod |>
  features(Production, features = guerrero)

# Apply Box-Cox transformation and first differencing
electric_prod_stationary <- electric_prod |>
  mutate(
    box_cox = box_cox(Production, lambda)
  )

# Plot the transformed series
electric_prod_stationary |>
  pivot_longer(cols = c(Production, box_cox),
               names_to = "transformation",
               values_to = "value") |>
  ggplot(aes(x = Date, y = value)) +
  geom_line() +
  facet_wrap(~transformation, scales = "free_y") +
  labs(title = "Original and Transformed Electric Production",
       x = "Year",
       y = "Value")

# Save the transformation plot
ggsave(paste0(folder_path, "/electric_prod_transformations.png"), 
       width = 12, height = 8, dpi = 300)


electric_prod_boxcox_ma <- electric_prod_stationary |>
  select(Date, box_cox) |>
  mutate(
    MA = slider::slide_dbl(box_cox, mean, .before = 11, .after = 0, .complete = TRUE),
    Production = box_cox - MA
  ) |>
  select(Date, Production)

#plot the detrended data
ggplot(electric_prod_boxcox_ma) +
  geom_line(aes(x = Date, y = Production), color = "blue") +
  labs(title = "Detrended Electric Production",
       x = "Year",
       y = "Production Index")

electric_prod_box_ma_ed_mean <- electric_prod_boxcox_ma |>
  mutate(
    EMA = EMA(Production, n = 12, ratio = 0)
  )

ed_mean = mean(electric_prod_box_ma_ed_mean$EMA, na.rm = TRUE)

electric_prod_box_ma_ed <- electric_prod_box_ma_ed_mean |>
  mutate(
    Production = Production - ed_mean
  ) |>
  select(Date, Production)
  

electric_prod_box_ma_ed |>
  ggplot(aes(x = Date, y = Production)) +
  geom_line(color = "blue") +
  labs(title = "Detrended Electric Production with Exponential Decay",
       x = "Year",
       y = "Production Index")

#perform ADF-test again
electric_prod_box_ma_ed |>
  mutate(
    Date = yearmonth(Date),
    Production = replace_na(Production, 0)
  ) |>
  index_by(Date) |>
  pull(Production) |>
  adf.test(k=12)
#Model Selection

arima_fit <- electric_prod |>
  mutate(Date = yearmonth(Date)) |>
  index_by(Date) |>
  summarise(Production = mean(Production)) |>
  select(Date, Production) |>
  model(
    auto_arima = ARIMA(Production)
  )

# Check model summary
report(arima_fit)

# Get residuals from ARIMA model
arima_residuals <- augment(arima_fit)$.resid

# ADF test on ARIMA residuals
adf_residuals <- adf.test(arima_residuals)
print("ADF Test on ARIMA Residuals:")
print(adf_residuals)

# Generate forecasts
arima_forecast <- arima_fit |>
  forecast(h = "1 year")

# Plot the forecasts
arima_forecast |>
  autoplot(electric_prod) +
  labs(
    title = "ARIMA Forecast for Electric Production",
    x = "Year",
    y = "Production Index"
  ) +
  theme_minimal() +
  theme(
    axis.text.x = element_text(angle = 0),
    legend.position = "bottom"
  )

# Save the forecast plot
ggsave(paste0(folder_path, "/electric_prod_forecast.png"),
       width = 10, height = 6, dpi = 300)

electric_prod <- electric_prod |>
  mutate(Date = yearmonth(Date)) |>
  index_by(Date) |>
  summarise(Production = mean(Production)) |>
  select(Date, Production)

simple_models <- electric_prod |>
  model(
    Mean = MEAN(Production),
    Naive = NAIVE(Production),
    SNaive = SNAIVE(Production ~ lag("year")),
    Drift = RW(Production ~ drift())
  )

# Generate forecasts for each method
simple_forecasts <- simple_models |>
  forecast(h = "1 year")

# Plot all forecasts
simple_forecasts |>
  autoplot(electric_prod, level = NULL) +
  labs(
    title = "Comparison of Simple Forecasting Methods",
    x = "Year",
    y = "Production Index"
  ) +
  theme_minimal()

# Save the comparison plot
ggsave(paste0(folder_path, "/simple_forecasts_comparison.png"), 
       width = 10, height = 6, dpi = 300)

# Get fitted values and residuals for each model
augmented <- simple_models |>
  augment()

# Residual diagnostics
residual_plots <- augmented |>
  pivot_longer(
    cols = c(.fitted, .resid),
    names_to = "type",
    values_to = "value"
  ) |>
  ggplot(aes(x = Date, y = value)) +
  geom_line() +
  facet_grid(type ~ .model, scales = "free_y") +
  labs(title = "Fitted Values and Residuals for Each Model") +
  theme_minimal()

# Save residual plots
ggsave(paste0(folder_path, "/residual_diagnostics.png"), 
       width = 12, height = 8, dpi = 300)

# Ljung-Box and Box-Pierce tests for each model
for(model_name in c("Mean", "Naive", "SNaive", "Drift")) {
  residuals <- augmented |>
    filter(.model == model_name) |>
    pull(.resid)
  
  cat("\nModel:", model_name, "\n")
  cat("Ljung-Box test:\n")
  print(Box.test(residuals, type = "Ljung-Box"))
  cat("Box-Pierce test:\n")
  print(Box.test(residuals, type = "Box-Pierce"))
}
# Simple Forecasting Methods:
# MEAN: Forecasts using the historical mean
# NAIVE: Uses the last observed value for all forecasts
# SNAIVE: Seasonal naive method using the value from the same season last year
# Drift: Allows the forecasts to increase or decrease over time by the average change
# Fitted Values and Residuals:
# Fitted values show what each model predicted for the historical data
# Residuals are the differences between actual and fitted values
# The plots help visualize how well each model fits the data
# Autocorrelation Tests:
# Ljung-Box and Box-Pierce tests check for autocorrelation in residuals
# Null hypothesis: Residuals are independently distributed
# If p-value < 0.05, residuals have significant autocorrelation (model might be inadequate)
# Box-Pierce is simpler but Ljung-Box is generally preferred for small samples
# The output will help you:
# Compare the accuracy of different forecasting methods
# Check if residuals look random (they should)
# Determine if there's remaining autocorrelation in residuals (there shouldn't be)
# Choose the best simple forecasting method for your data


extended_models <- electric_prod |>
  model(
    # Simple methods (already used)
    Mean = MEAN(Production),
    Naive = NAIVE(Production),
    SNaive = SNAIVE(Production ~ lag("year")),
    Drift = RW(Production ~ drift()),
    
    # Exponential Smoothing methods
    ETS_ANN = ETS(Production ~ error("A") + trend("N") + season("N")),
    ETS_AAN = ETS(Production ~ error("A") + trend("A") + season("N")),
    ETS_Auto = ETS(Production),  # Automatic selection
    
    # ARIMA variants
    ARIMA_Auto = ARIMA(Production),  # Automatic ARIMA
    ARIMA_201 = ARIMA(Production ~ pdq(2,0,1)),  # Manual ARIMA specification
    
    # Neural Network methods
    NNETAR = NNETAR(Production),
    
    # Regression based
    TSLM = TSLM(Production ~ trend() + season()),
    
    # Prophet model (Facebook's forecasting tool)
    Prophet = prophet(Production ~ season("year"))
  )

# Generate forecasts
extended_forecasts <- extended_models |>
  forecast(h = "1 year")

# Compare accuracy of all models
accuracy_comparison <- accuracy(extended_forecasts, electric_prod)
print(accuracy_comparison)

# Plot forecasts from all models
extended_forecasts |>
  autoplot(electric_prod, level = NULL) +
  labs(
    title = "Comparison of Different Forecasting Methods",
    x = "Year",
    y = "Production Index"
  ) +
  theme_minimal() +
  theme(legend.position = "bottom")

# Save the comparison plot
ggsave(paste0(folder_path, "/extended_forecasts_comparison.png"), 
       width = 12, height = 8, dpi = 300)


# Exponential Smoothing (ETS):
# ETS_ANN: Simple exponential smoothing
# ETS_AAN: Holt's linear method
# ETS_Auto: Automatic selection of best ETS model
# Good for data with trend and/or seasonal patterns
# ARIMA Variants:
# ARIMA_Auto: Automatic ARIMA selection
# ARIMA_201: Manual ARIMA specification
# Good for stationary data or data that can be made stationary
# Neural Network (NNETAR):
# Neural network time series forecasts
# Good for complex, non-linear patterns
# Can capture relationships that linear models miss
# 4. Regression Based (TSLM):
# Time series linear regression
# Includes trend and seasonal components
# Good for simple linear relationships
# 5. Prophet:
# Facebook's forecasting tool
# Handles seasonality and holidays well
# Good for daily data with strong seasonal patterns
# The code also includes:
# Visualization of all forecasts