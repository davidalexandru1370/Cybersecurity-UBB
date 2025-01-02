library(fpp3)
library(tidyverse)
library(tseries)

folder_path <- "../Desktop/folders/Cybersecurity-UBB/Forecasting/Report"
electricity_data_df <- read_csv(paste0(folder_path, "/Electric_Production.csv"), col_names = TRUE)


electric_prod <- electricity_data |>
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

adf.test(electric_prod$Production)
#The p-value of 0.01 is less than the common significance level of 0.05.
#This indicates that we can reject the null hypothesis.
#This implies that the time series is stationary.

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