library(tidyverse)
library(fpp3)

?us_change
us_change

us_change |>
    pivot_longer(c(Consumption, Income), names_to = "Series") |>
  autoplot(value, size = 1)
ggsave("Us_Change_Plot.png")


us_change |>
  ggplot(mapping = aes(x = Income, y = Consumption)) +
  geom_point( size = 3) +
  geom_smooth(method = "lm", se = FALSE)
ggsave("us_change_scatter.png")

us_change |>
  model(lm = TSLM(Consumption ~ Income)) |>
  report()

us_change |>
  model(TSLM(Consumption ~ Income + Savings)) |> tidy()


us_change |>
  model(TSLM(Consumption ~ Income + Savings)) |> report()


us_change |>
  pivot_longer(c(Consumption, Income, Production, Savings, Unemployment), names_to = "Series") |>
  autoplot(value, size = 1) +
  facet_wrap(vars(Series), nrow = 5, scales = "free")
ggsave("Us_Change_All_Plot.png")

us_change |> GGally::ggpairs(columns = 2:6)
ggsave("us_change_ggpairs.png")

us_change |>
  model(TSLM(Consumption ~ Income + Unemployment)) |> report()

us_change |>
  ggplot(mapping = aes(x = Income, y = Consumption)) +
  geom_point( size = 3) +
  geom_smooth(method = "lm", se = FALSE, linewidth = 1.5) +
  geom_abline(intercept = 0.5, slope = 0.3, color = "red", linewidth = 1.5) +
  geom_abline(intercept = 0.6, slope = 0.2, color = "brown", linewidth = 1.5)
ggsave("us_change_lines.png")

us_change |>
  model(TSLM(Consumption ~ Income + Production + Unemployment + Savings + Unemployment)) |> report()

us_change |>
  model(TSLM(Consumption ~ 0 + Income + Production + Unemployment + Savings + Unemployment)) |> report()


us_change |> 
  model(TSLM(Consumption ~ Income + Savings + Unemployment + Production)) |> 
  augment() |>
  ggplot(mapping = aes(x = Quarter)) +
  geom_line(mapping = aes(y = Consumption, color = "Data"), linewidth = 1.5) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted"), linewidth = 1.5) +
  guides(color = guide_legend(title = NULL)) 
ggsave("us_change_fitted.png")

us_change |>
  model(TSLM(Consumption ~ Income + Savings + Unemployment + Production)) |> 
  augment() |> 
  ggplot(mapping = aes(x = Consumption, y = .fitted)) +
  geom_point(size = 2) +
  geom_abline(intercept = 0, slope = 1, linewidth = 1.5, color = "red") 
ggsave("us_change_fitted_Scatter.png")

us_change |>
  model(TSLM(Consumption ~ Income)) |>
  report()


us_change_model <- us_change |>
  model(all = TSLM(Consumption ~ Unemployment + Income))

p <- us_change_model |> gg_tsresiduals()
p
ggsave("us_change_resid_diag.png", plot = p)

us_change_resid <- us_change_model |> augment()
us_change_resid

us_change |>
  left_join(us_change_resid, by = "Quarter") |>
  pivot_longer(c(Income, Unemployment, Savings, Production), names_to = "predictor", values_to = "x") |>
  ggplot(mapping = aes(x = x, y = .resid)) +
  geom_point() +
  facet_wrap(vars(predictor), scales = "free") 
ggsave("us_change_resid_scatter.png")

us_change_model |> report()
us_change |>
  model(all = TSLM(Consumption ~ Unemployment + Income + Production)) |> report()

us_change_resid |>
  ggplot(mapping = aes(x = .fitted, y = .resid)) +
  geom_point(size = 2) 
ggsave("us_change_resid_vs_fitted.png")

library(cowplot)

aus_airpassengers
guinea_rice

autoplot(aus_airpassengers) -> p1
autoplot(guinea_rice) -> p2

plot_grid(p1, p2, nrow = 2) #requires library cowplot
ggsave("Passengers_rice_plot.png")

cor(aus_airpassengers$Passengers |> head(n = 42), guinea_rice$Production)


#merge them in one tsibble
joined <- aus_airpassengers |>
  head(n = 42) |>
  left_join(guinea_rice, by = "Year")

joined |> 
  ggplot(mapping = aes(x = Passengers, y = Production)) +
  geom_point(size = 2) 
ggsave("Passengers_rice_scatter.png")

model <- joined |>
  model(model = TSLM(Passengers ~ Production))

model |> report()
p <- model |> gg_tsresiduals() 
p
ggsave("Passengers_rice_resid_diag.png", plot = p)

model |> 
  augment() |> 
  features(.innov, ljung_box, lag = 8) #lag should be minimum between 10 and T/5

#trend as predictor
aus_airpassengers |> autoplot() + geom_point()
ggsave("air_passengers_plot.png")

air_model <- aus_airpassengers |>
  model(m = TSLM(Passengers ~ trend()))
air_model |> report()

air_model |> 
  gg_tsresiduals() -> p
p
ggsave("air_passengers_resid_diag.png", plot = p)


aus_production
recent_production <- aus_production |>
  filter(year (Quarter) >= 1992)

recent_production |>
  autoplot(Beer) +
  geom_point()
ggsave("beer_production_plot.png")

beer_fit <- recent_production |>
  model(TSLM(Beer ~ trend() + season()))
report(beer_fit)

beer_fit |> 
  gg_tsresiduals() -> p
p
ggsave("beer_production_resid_diag.png", plot = p)

beer_fit |> 
  augment() |> 
  features(.innov, ljung_box, lag = 8) #white noise 

beer_fit |> augment() |>
  ggplot(mapping = aes(x = Quarter)) +
  geom_line(mapping = aes(y = Beer, colour = "Actual"), linewidth = 1) +
  geom_line(mapping = aes(y = .fitted, colour = "Fitted"), linewidth = 1) +
  guides(colour = guide_legend(title = "Series")) 
ggsave("beer_production_actual_vs_fitted.png")

beer_fit |> augment() |>
  ggplot() +
  geom_point(mapping = aes(x = Beer, y = .fitted, colour = factor(quarter(Quarter)))) +
  geom_abline(intercept = 0, slope = 1) +
  scale_color_manual(values = c( "red", "blue", "green", "black")) +
  guides (colour = guide_legend("Title")) 
ggsave("beer_production_actual_vs_fitted_scatter.png")  

beer_fit |> augment() |>
  ggplot() +
  geom_point(mapping = aes(x = .innov, y = .fitted, colour = factor(quarter(Quarter))), size = 5) +
  scale_color_manual(values = c( "red", "blue", "green", "black")) +
  guides (colour = guide_legend("Title")) 
ggsave("beer_production_innov_vs_fitted_scatter.png")

vic_elec
vic_elec_model <- vic_elec |> model(TSLM(Demand ~ Temperature + Holiday))
vic_elec_model |> report()

vic_elec |> mutate (Day = weekdays(Time)) -> vic_elec_day
vic_elec_day

vic_elec_model2 <- vic_elec_day |> model(TSLM(Demand ~ Temperature + Holiday + Day ))
vic_elec_model2 |> report()

vic_elec |> 
  model(TSLM(Demand ~ Temperature + fourier(period = 48, K = 3))) |>
  report()

aus_retail
aus_cafe <- aus_retail |>
  filter(Industry == "Cafes, restaurants and takeaway food services", 
         year(Month) >= 2004, year(Month) <= 2018) |>
  summarise(Turnover = sum(Turnover))
aus_cafe
aus_cafe |> autoplot() + geom_point()
ggsave("aus_cafe_plot.png")

fit <- aus_cafe |>
  model(
    K1 = TSLM(log(Turnover) ~ trend() + fourier(K = 1)),
    K2 = TSLM(log(Turnover) ~ trend() + fourier(K = 2)),
    K3 = TSLM(log(Turnover) ~ trend() + fourier(K = 3)),
    K4 = TSLM(log(Turnover) ~ trend() + fourier(K = 4)),
    K5 = TSLM(log(Turnover) ~ trend() + fourier(K = 5)),
    K6 = TSLM(log(Turnover) ~ trend() + fourier(K = 6)),
  )

fit |> forecast(h = 24) -> cafe_forecast
fit |> augment() -> fit_aug


cafe_forecast |> filter(.model == "K1") |> 
  autoplot(linewidth = 1.5) +
  autolayer(aus_cafe, Turnover, linewidth = 1) +
  autolayer(fit_aug |> filter(.model == "K1"), .fitted, color = "red", linewidth = 1.5)
ggsave("aus_cafe_fourier_k1.png")

cafe_forecast |> filter(.model == "K2") |> 
  autoplot(linewidth = 1.5) +
  autolayer(aus_cafe, Turnover, linewidth = 1) +
  autolayer(fit_aug |> filter(.model == "K2"), .fitted, color = "red", linewidth = 1.5)
ggsave("aus_cafe_fourier_k2.png")


cafe_forecast |> filter(.model == "K3") |> 
  autoplot(linewidth = 1.5) +
  autolayer(aus_cafe, Turnover, linewidth = 1) +
  autolayer(fit_aug |> filter(.model == "K3"), .fitted, color = "red", linewidth = 1.5)
ggsave("aus_cafe_fourier_k3.png")


cafe_forecast |> filter(.model == "K4") |> 
  autoplot(linewidth = 1.5) +
  autolayer(aus_cafe, Turnover, linewidth = 1) +
  autolayer(fit_aug |> filter(.model == "K4"), .fitted, color = "red", linewidth = 1.5)
ggsave("aus_cafe_fourier_k4.png")


cafe_forecast |> filter(.model == "K5") |> 
  autoplot(linewidth = 1.5) +
  autolayer(aus_cafe, Turnover, linewidth = 1) +
  autolayer(fit_aug |> filter(.model == "K5"), .fitted, color = "red", linewidth = 1.5)
ggsave("aus_cafe_fourier_k5.png")


cafe_forecast |> filter(.model == "K6") |> 
  autoplot(linewidth = 1.5) +
  autolayer(aus_cafe, Turnover, linewidth = 1) +
  autolayer(fit_aug |> filter(.model == "K6"), .fitted, color = "red", linewidth = 1.2)
ggsave("aus_cafe_fourier_k6.png")


glance(fit) |> select(.model, r_squared, adj_r_squared, CV, AICc)

recent_beer |> model(TSLM(Beer ~ trend()  + season())) |> 
  forecast() |> autoplot(recent_beer, linewidth = 1.5)
ggsave("beer_forecast.png")


consumptionFit <- us_change |>
  model(all = TSLM(Consumption ~ Income + Savings + Unemployment))

future_scenarios <- scenarios(
  increase = new_data(us_change, 4) |>
    mutate(Income = 1, Savings = 0.5, Unemployment = 0),
  decrease = new_data(us_change, 4) |>
    mutate(Income=-1, Savings = -0.5, Unemployment = 0),
  names_to = "Scenarios"
)

future_scenarios

consumptionForecast <- forecast(consumptionFit, new_data = future_scenarios)
consumptionForecast |> view()
us_change |>
  autoplot(Consumption) +
  autolayer(consumptionForecast)  
ggsave("consumption_forecast.png")

vitamins <- PBS |> 
  filter(ATC2 == "A11") |>
  select(Month, Concession, Type, Cost) |>
  summarize(TotalCost = sum(Cost)) |>
  mutate(Cost = TotalCost / 1000000)

autoplot(vitamins, Cost) +
  geom_point()
ggsave("vitamins_plot.png")

vitamins_model1 <- vitamins |>
  model(TSLM(Cost ~ trend()))
vitamins_model1 |> report()

vitamins |> ggplot(mapping = aes(x = Month, y = Cost)) +
  geom_line() +
  geom_line(data = fitted(vitamins_model1), aes(y = .fitted, colour = .model), linewidth = 1.5) 
ggsave("vitamins_model.png")

vitamins_model2 <- vitamins |> 
  model(TSLM(Cost ~ trend(knots = yearmonth("2000 Jan"))))
vitamins_model |> report()

vitamins |> ggplot(mapping = aes(x = Month, y = Cost)) +
  geom_line() +
  geom_line(data = fitted(vitamins_model2), aes(y = .fitted, colour = .model), linewidth=1.5)
ggsave("vitamins_model_with_knots.png")

boston_marathon |> 
  filter(Year >= 1924) |>
  filter(Event == "Men's open division") |> 
  mutate(Minutes = as.numeric(Time)/60) ->boston_men

boston_men
boston_men |> autoplot(Minutes) +
  geom_point()
ggsave("boston_marathon_plot.png")

boston_model <- boston_men |>
  model(linear = TSLM(Minutes ~ trend()), 
        logarithmic = TSLM(log(Minutes) ~ trend()),
        piecewise = TSLM(Minutes ~ trend(knots = c(1950, 1980)))
  )
boston_model |> 
  accuracy() |> 
  arrange(MAE)       

boston_forecast <- boston_model |> forecast(h = 10)
boston_forecast

boston_men |>
  autoplot(Minutes) +
  autolayer(boston_forecast) +
  geom_line(data = fitted(boston_model), aes(y = .fitted, colour = .model)) 

ggsave("boston_marathon_forecast.png")
