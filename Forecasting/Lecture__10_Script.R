library(tidyverse)
library(fpp3)

global_economy
algeria_economy <- global_economy |>
  filter(Country == "Algeria")
algeria_economy |> autoplot() +
  geom_point()
ggsave("Algerian_economy_plot.png")

algeria_models <- algeria_economy |>
  model(m00 = ETS(Exports ~ error("A") + trend("N", alpha = 0.0001) + season("N")),
        m05 = ETS(Exports ~ error("A") + trend("N", alpha = 0.05) + season("N")),
        m10 = ETS(Exports ~ error("A") + trend("N", alpha = 0.1) + season("N")),
        m20 = ETS(Exports ~ error("A") + trend("N", alpha = 0.20) + season("N")),
        m30 = ETS(Exports ~ error("A") + trend("N", alpha = 0.30) + season("N")),
        m40 = ETS(Exports ~ error("A") + trend("N", alpha = 0.40) + season("N")),
        m50 = ETS(Exports ~ error("A") + trend("N", alpha = 0.50) + season("N")),
        m60 = ETS(Exports ~ error("A") + trend("N", alpha = 0.60) + season("N")),
        m70 = ETS(Exports ~ error("A") + trend("N", alpha = 0.70) + season("N")),
        m80 = ETS(Exports ~ error("A") + trend("N", alpha = 0.80) + season("N")),
        m90 = ETS(Exports ~ error("A") + trend("N", alpha = 0.90) + season("N")),
        m100 = ETS(Exports ~ error("A") + trend("N", alpha = 0.999) + season("N"))) 
                  
 algeria_models |> tidy()
algeria_models |> augment()

algeria_models |> augment() |> 
  filter(.model == "m00") |> ggplot(mapping = aes(x = Year)) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted")) + 
  geom_line(mapping = aes(y = algeria_economy$Exports, color = "Actual")) +
  guides (colour = guide_legend("Series"))
ggsave("Alpha0001.png")

algeria_models |> augment() |> 
  filter(.model == "m05") |> ggplot(mapping = aes(x = Year)) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted")) + 
  geom_line(mapping = aes(y = algeria_economy$Exports, color = "Actual")) +
  guides (colour = guide_legend("Series"))
ggsave("Alpha05.png")

algeria_models |> augment() |> 
  filter(.model == "m10") |> ggplot(mapping = aes(x = Year)) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted")) + 
  geom_line(mapping = aes(y = algeria_economy$Exports, color = "Actual")) +
  guides (colour = guide_legend("Series"))
ggsave("Alpha10.png")


algeria_models |> augment() |> 
  filter(.model == "m20") |> ggplot(mapping = aes(x = Year)) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted")) + 
  geom_line(mapping = aes(y = algeria_economy$Exports, color = "Actual")) +
  guides (colour = guide_legend("Series"))
ggsave("Alpha20.png")


algeria_models |> augment() |> 
  filter(.model == "m30") |> ggplot(mapping = aes(x = Year)) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted")) + 
  geom_line(mapping = aes(y = algeria_economy$Exports, color = "Actual")) +
  guides (colour = guide_legend("Series"))
ggsave("Alpha30.png")

algeria_models |> augment() |> 
  filter(.model == "m40") |> ggplot(mapping = aes(x = Year)) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted")) + 
  geom_line(mapping = aes(y = algeria_economy$Exports, color = "Actual")) +
  guides (colour = guide_legend("Series"))
ggsave("Alph40.png")

algeria_models |> augment() |> 
  filter(.model == "m50") |> ggplot(mapping = aes(x = Year)) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted")) + 
  geom_line(mapping = aes(y = algeria_economy$Exports, color = "Actual")) +
  guides (colour = guide_legend("Series"))
ggsave("Alpha50.png")

algeria_models |> augment() |> 
  filter(.model == "m60") |> ggplot(mapping = aes(x = Year)) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted")) + 
  geom_line(mapping = aes(y = algeria_economy$Exports, color = "Actual")) +
  guides (colour = guide_legend("Series"))
ggsave("Alpha60.png")

algeria_models |> augment() |> 
  filter(.model == "m70") |> ggplot(mapping = aes(x = Year)) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted")) + 
  geom_line(mapping = aes(y = algeria_economy$Exports, color = "Actual")) +
  guides (colour = guide_legend("Series"))
ggsave("Alpha70.png")

algeria_models |> augment() |> 
  filter(.model == "m80") |> ggplot(mapping = aes(x = Year)) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted")) + 
  geom_line(mapping = aes(y = algeria_economy$Exports, color = "Actual")) +
  guides (colour = guide_legend("Series"))
ggsave("Alpha80.png")

algeria_models |> augment() |> 
  filter(.model == "m90") |> ggplot(mapping = aes(x = Year)) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted")) + 
  geom_line(mapping = aes(y = algeria_economy$Exports, color = "Actual")) +
  guides (colour = guide_legend("Series"))
ggsave("Alpha90.png")

algeria_models |> augment() |> 
  filter(.model == "m100") |> ggplot(mapping = aes(x = Year)) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted")) + 
  geom_line(mapping = aes(y = algeria_economy$Exports, color = "Actual")) +
  guides (colour = guide_legend("Series"))
ggsave("Alpha100.png")


algeria_model <- algeria_economy |>
  model(ANN = ETS(Exports ~ error("A") + trend("N") + season("N")))
algeria_model |> report()

algeria_model |> tidy()
algeria_forecast <- algeria_model |>
  forecast(h = 5)
algeria_forecast

algeria_forecast |>
  autoplot(algeria_economy) +
  geom_line(mapping = aes(y =.fitted), data = augment(algeria_model), col = "red") 
ggsave("Algerian_economy_fitted_values.png")

#trend
aus_economy <- global_economy |>
  filter(Code == "AUS") |>
  mutate(Pop = Population / 1e6)

aus_economy |> autoplot(Pop) + geom_point()
ggsave("Aus_Population_plot.png")


aus_economy_models <- aus_economy |>
  model(m00 = ETS(Pop ~ error("A") + trend("A", alpha = 0.001, alpha_range = c(-1, 1), beta = 0.001) + season("N"), bounds = "admissible"),
      m01 = ETS(Pop ~ error("A") + trend("A", alpha = 0.001, alpha_range = c(-1, 1), beta = 0.1) + season("N"), bounds = "admissible"),
      m02 = ETS(Pop ~ error("A") + trend("A", alpha = 0.001, alpha_range = c(-1, 1), beta = 0.2) + season("N"), bounds = "admissible"),
      m03 = ETS(Pop ~ error("A") + trend("A", alpha = 0.001, alpha_range = c(-1, 1), beta = 0.3) + season("N"), bounds = "admissible"),
      m04 = ETS(Pop ~ error("A") + trend("A", alpha = 0.001, alpha_range = c(-1, 1), beta = 0.4) + season("N"), bounds = "admissible"),
      m05 = ETS(Pop ~ error("A") + trend("A", alpha = 0.001, alpha_range = c(-1, 1), beta = 0.5) + season("N"), bounds = "admissible"),
      m06 = ETS(Pop ~ error("A") + trend("A", alpha = 0.001, alpha_range = c(-1, 1), beta = 0.6) + season("N"), bounds = "admissible"),
      m07 = ETS(Pop ~ error("A") + trend("A", alpha = 0.001, alpha_range = c(-1, 1), beta = 0.7) + season("N"), bounds = "admissible"),
      m08 = ETS(Pop ~ error("A") + trend("A", alpha = 0.001, alpha_range = c(-1, 1), beta = 0.8) + season("N"), bounds = "admissible"),
      m09 = ETS(Pop ~ error("A") + trend("A", alpha = 0.001, alpha_range = c(-1, 1), beta = 0.9) + season("N"), bounds = "admissible"),
      m010 = ETS(Pop ~ error("A") + trend("A", alpha = 0.001, alpha_range = c(-1, 1), beta = 1) + season("N"), bounds = "admissible"))

aus_economy_models
algeria_models |> augment()

aus_economy_models |> augment() |> 
  filter(.model == "m00") |> ggplot(mapping = aes(x = Year)) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted"), linewidth = 1.3) + 
  geom_line(mapping = aes(y = aus_economy$Pop, color = "Actual")) +
  guides (colour = guide_legend("Series"))
ggsave("AUS_Alpha0001.png")

aus_economy_models |> augment() |> 
  filter(.model == "m01") |> ggplot(mapping = aes(x = Year)) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted"), linewidth = 1.3) + 
  geom_line(mapping = aes(y = aus_economy$Pop, color = "Actual")) +
  guides (colour = guide_legend("Series"))
ggsave("AUS_Alpha01.png")

aus_economy_models |> augment() |> 
  filter(.model == "m02") |> ggplot(mapping = aes(x = Year)) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted"), linewidth = 1.3) + 
  geom_line(mapping = aes(y = aus_economy$Pop, color = "Actual")) +
  guides (colour = guide_legend("Series"))
ggsave("AUS_Alpha20.png")

aus_economy_models |> augment() |> 
  filter(.model == "m03") |> ggplot(mapping = aes(x = Year)) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted"), linewidth = 1.3) + 
  geom_line(mapping = aes(y = aus_economy$Pop, color = "Actual")) +
  guides (colour = guide_legend("Series"))
ggsave("AUS_Alpha30.png")

aus_economy_models |> augment() |> 
  filter(.model == "m04") |> ggplot(mapping = aes(x = Year)) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted"), linewidth = 1.3) + 
  geom_line(mapping = aes(y = aus_economy$Pop, color = "Actual")) +
  guides (colour = guide_legend("Series"))
ggsave("AUS_Alph40.png")

aus_economy_models |> augment() |> 
  filter(.model == "m05") |> ggplot(mapping = aes(x = Year)) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted"), linewidth = 1.3) + 
  geom_line(mapping = aes(y = aus_economy$Pop, color = "Actual")) +
  guides (colour = guide_legend("Series"))
ggsave("AUS_Alpha50.png")

aus_economy_models |> augment() |> 
  filter(.model == "m06") |> ggplot(mapping = aes(x = Year)) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted"), linewidth = 1.3) + 
  geom_line(mapping = aes(y = aus_economy$Pop, color = "Actual")) +
  guides (colour = guide_legend("Series"))
ggsave("AUS_Alpha60.png")

aus_economy_models |> augment() |> 
  filter(.model == "m07") |> ggplot(mapping = aes(x = Year)) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted"),linewidth = 1.3) + 
  geom_line(mapping = aes(y = aus_economy$Pop, color = "Actual")) +
  guides (colour = guide_legend("Series"))
ggsave("AUS_Alpha70.png")

aus_economy_models |> augment() |> 
  filter(.model == "m08") |> ggplot(mapping = aes(x = Year)) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted"),linewidth = 1.3) + 
  geom_line(mapping = aes(y = aus_economy$Pop, color = "Actual")) +
  guides (colour = guide_legend("Series"))
ggsave("AUS_Alpha80.png")

aus_economy_models |> augment() |> 
  filter(.model == "m09") |> ggplot(mapping = aes(x = Year)) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted"),linewidth = 1.3) + 
  geom_line(mapping = aes(y = aus_economy$Pop, color = "Actual")) +
  guides (colour = guide_legend("Series"))
ggsave("AUS_Alpha90.png")

aus_economy_models |> augment() |> 
  filter(.model == "m010") |> ggplot(mapping = aes(x = Year)) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted"), linewidth = 1.3) + 
  geom_line(mapping = aes(y = aus_economy$Pop, color = "Actual")) +
  guides (colour = guide_legend("Series"))
ggsave("AUS_Alpha010.png")

fit <- aus_economy |>
  model(AAN = ETS(Pop ~ error("A") + trend("A") + season("N")))
fit |> report()
fit |> tidy()

fit|> components()


fit |> components()  |>
  autoplot()
ggsave("Aus_Pop_Components.png")

augment(fit)
fitted(fit)

fit |> components() |>
  left_join(fitted(fit), by= c("Country", ".model", "Year"))

fit_forecast <- fit |>
  forecast(h = 10)

fit_augmented <- fit |> augment()

fit_forecast |> autoplot() + 
  autolayer(aus_economy, Pop) +
  autolayer(fit_augmented, .fitted, color = "red") 
ggsave("Aus_pop_forecast.png")


aus_economy_damped <-aus_economy |>
  model(Holt = ETS(Pop ~ error("A") + trend("A") + season("N")), 
        Damped = ETS(Pop ~ error("A") + trend("Ad", phi = 0.8) + season("N"))) #AD - additive damped
aus_economy_damped |> tidy() #function report does not work for multiple models

aus_economy_damped |> augment() |> view()

aus_economy_damped_forecast <- aus_economy_damped |> forecast(h = 15)

aus_economy_damped_forecast |> autoplot(aus_economy, level = NULL, linewidth=1.3)
ggsave("Aus_Pop_Damped08.png")


aus_economy_damped <-aus_economy |>
  model(Holt = ETS(Pop ~ error("A") + trend("A") + season("N")), 
        Damped = ETS(Pop ~ error("A") + trend("Ad", phi = 0.98) + season("N"))) #AD - additive damped
aus_economy_damped |> tidy() #function report does not work for multiple models

aus_economy_damped |> augment() |> view()

aus_economy_damped_forecast <- aus_economy_damped |> forecast(h = 15)

aus_economy_damped_forecast |> autoplot(aus_economy, level = NULL, linewidth=1.3)
ggsave("Aus_Pop_Damped98.png")


#Example
www_usage <- WWWusage |> as_tsibble() 
www_usage_cv <- www_usage |> 
  stretch_tsibble(.init = 10)

www_usage |> autoplot() +
  geom_point()
ggsave("WWUsage_Plot.png")

www_usage_model <- www_usage_cv |>
  model(SES = ETS(value ~ error("A") + trend("N") + season("N")),
        Holt = ETS(value ~ error("A") + trend("A") + season("N")),
        Damped = ETS(value ~ error("A") + trend("Ad") + season("N")))  

www_usage_model |> 
  forecast(h = 1) |> 
  accuracy(www_usage)

www_usage |> 
  model(ETS(value ~ error("A") + trend("Ad") + season("N"))) |> report()

www_usage |> 
  model(ETS(value ~ error("A") + trend("Ad") + season("N"))) |>
  forecast(h = 10) |> 
  autoplot(www_usage)
ggsave("WWUsage_Damped_forecast.png")


#train-test
www_usage_train <- www_usage |> 
  head(n = 80)
www_usage_test <- www_usage |> 
  tail(n= 20)

www_usage_model2 <- www_usage_train |>
  model(SES = ETS(value ~ error("A") + trend("N") + season("N")),
        Holt = ETS(value ~ error("A") + trend("A") + season("N")),
        Damped = ETS(value ~ error("A") + trend("Ad", phi = 0.8) + season("N")))  #try phi = 0.8, 0.9. 0.98

www_usage_model2 |> 
  forecast(h = 20) |> 
  accuracy(www_usage_test)

www_usage_train |> model(Holt = ETS(value ~ error("A") + trend("A") + season("N"))) |> report()

www_usage_model2 |> 
  forecast(h = 20) |> 
  autoplot(www_usage, level = NULL, linewidth = 1.3) 
ggsave("wwUsage_Holt_Forecast.png")


#trend + season

aus_holidays <- tourism |> 
  filter(Purpose == "Holiday") |>
  summarise(Trips = sum(Trips) / 1e3)
aus_holidays

aus_holidays |> autoplot() + 
  geom_point()
ggsave("Aus_holiday_plot.png")

aus_holidays_model <- aus_holidays |>
  model(additive = ETS(Trips ~ error("A") + trend("A") + season("A")),
        multiplicative = ETS(Trips ~ error("A") + trend("A") + season("M")))

aus_holidays_model |> tidy()

aus_holidays_forecast <- aus_holidays_model |>
  forecast(h = "3 years")

aus_holidays_forecast |> 
  autoplot(aus_holidays, level = NULL) 
ggsave("Aus_holiday_Forecasts.png")

aus_holidays_model[2] |> augment() |> autoplot(.fitted, color = "red", linewidth = 1.5) +
  autolayer(aus_holidays_model[1] |> augment(), .fitted, color = "blue", linewidth = 1.5) +  
  autolayer(aus_holidays, color = "black", linewidth =2) 

p <- aus_holidays_model[1] |> gg_tsresiduals() #additive
p  
ggsave("Aus_holiday_additive_resid.png", plot = p)

p <- aus_holidays_model[2] |> gg_tsresiduals() # multiplicative
p
ggsave("Aus_holiday_multiplicative_resid.png", plot = p)


aus_holidays_model[1] |> augment() |> autoplot(.fitted, color = "red", linewidth = 1.5) +
  autolayer(aus_holidays, color = "black", linewidth =2) +
  autolayer(aus_holidays_model[2] |> augment(), .fitted, color = "blue", linewidth = 1.5)


aus_holidays_model[1] |> 
  components() |> autoplot() 
ggsave("Aus_holiday_additive_components.png")

aus_holidays_model[2] |> 
  components() |> autoplot() 
ggsave("Aus_holiday_multiplicative_components.png")

pedestrian #two years, hourly data

#pick second half of 2016 and aggregate into daily
pedestrian_short <- pedestrian |>
  filter(Date >= "2016-07-10", Sensor == "Southern Cross Station") |>
  index_by (Date) |>
  summarize(Count = sum(Count)/ 1000)

pedestrian_short  |> autoplot(Count)  + geom_point()
ggsave("Pedestrian_plot.png")
pedestrian_short |> gg_season(period = "week")  #remember seasonal plot?
ggsave("Pedestrian_seasonal.png")
  
pedestrian_train <- pedestrian_short |>
  filter(Date <= "2016-07-31")
pedestrian_model <- pedestrian_train |>
  model(ETS(Count ~ error("A") + trend("Ad") + season("M"))) #Experiment with M and A 
pedestrian_forecast <- pedestrian_model |> 
  forecast(h = "2 weeks")

pedestrian_forecast |> autoplot(pedestrian_short |>
                                  filter(Date <= "2016-08-14")) 
ggsave("Pedestrian_forecast.png")

pedestrian_test <-pedestrian_short |>
  filter(Date >= "2016-08-01", Date <= "2016-08-14")

accuracy(pedestrian_forecast, data = pedestrian_test)

#Example 1
aus_holidays <- tourism |>
  filter(Purpose == "Holiday") |>
  summarize(Trips = sum(Trips)/1e3)
aus_holidays |> 
  autoplot() +
  geom_point()

aus_holidays_model <- aus_holidays |>
  model(ETS(Trips))
report(aus_holidays_model)


pedestrian_short <- pedestrian |>
  filter(Date >= "2016-07-10", Sensor == "Southern Cross Station") |>
  index_by (Date) |>
  summarize(Count = sum(Count)/ 1000)
pedestrian_model <- pedestrian_short |>
  model(ETS(Count))
pedestrian_model |> report()   

aus_economy <- global_economy |>
  filter(Code == "AUS") |>
  select(Population) |>
  mutate(Pop = Population / 1e6) #just to work with smaller values

aus_economy_model <- aus_economy |>
  model(ETS(Pop))
aus_economy_model |> report()    


#ARIMA
google_2015 <- gafa_stock |>
  filter(Symbol == "GOOG", year(Date) == 2015)

google_2015 |> autoplot(Close) + geom_point()

google_2015 |>
  features(Close, ljung_box, lag = 10)


google_2015 |>
  ACF(Close) |> 
  autoplot() 

google_2015 |> autoplot(difference(Close)) 

google_2015 |>
  ACF(difference(Close)) |>
  autoplot() 

#is the differenced data really white noise?
google_2015 |>
  mutate(diff = difference(Close)) |>
  features(diff, ljung_box, lag = 10)
#p = 0.637 => yes, it is.

PBS |>
  filter(ATC2 == "A10") |>
  summarize(Cost = sum(Cost)/ 1e6) -> antidiabetic
antidiabetic |> autoplot() + geom_point()

antidiabetic |> 
  mutate(diff = difference(Cost)) |>
  select(diff) -> antidiabetic2
antidiabetic2 |> autoplot(diff) 



antidiabetic2 |> 
  mutate(diffL = log(diff)) |>
  select(diffL) -> antidiabetic3
antidiabetic3 |> autoplot(diffL) 

#let's do it the other way around
antidiabetic |> 
  mutate(CostL = log(Cost)) |>
  select(CostL) -> antidiabetic4
antidiabetic4 |> autoplot(CostL) 
antidiabetic4 |> 
  mutate(CostLD = difference(CostL)) |>
  select(CostLD) -> antidiabetic5

antidiabetic5 |> autoplot(CostLD) 
antidiabetic |> 
  mutate(CostL = log(Cost)) |>
  select(CostL) -> antidiabetic7

antidiabetic7 |> autoplot(CostL) 

antidiabetic7 |> 
  mutate(CostLS = difference(CostL, 12)) |>
  select(CostLS) -> antidiabetic8

antidiabetic8 |> autoplot() 

antidiabetic8 |> 
  mutate(CostLSDif = difference(CostLS)) |>
  select(CostLSDif) -> antidiabetic9
antidiabetic9 |> autoplot() 
antidiabetic8 |> ACF(CostLS) |> autoplot() 

antidiabetic8 |>
  features(CostLS, ljung_box, lag = 24) # this is not white noise

antidiabetic9 |> ACF(CostLSDif) |> autoplot() 
antidiabetic9 |>
  features(CostLSDif, ljung_box, lag = 24) # this is not white noise

antidiabetic8 |>
  features(CostLS, unitroot_kpss) #p value below 0.05 means the data is not stationary

antidiabetic9 |>
  features(CostLSDif, unitroot_kpss) 

antidiabetic |>
  features(Cost, unitroot_ndiffs)

antidiabetic |>
  features(Cost, unitroot_nsdiffs)

