library(tidyverse)
library(fpp3)

aus_births
aus_births |> filter(State == "VIC") -> vic_births
vic_births
vic_births |> autoplot()
ggsave("VicBirthsPlot.png")

vic_births |> model(
  mean = MEAN(Births),
  naive = NAIVE(Births),
  s_naive = SNAIVE(Births ~lag(12)),
  drift = RW(Births ~ drift())) -> vic_births_models

vic_births_models
vic_births_models |> forecast( h = "2 years") -> vic_births_forecast

vic_births_forecast

vic_births_forecast |> autoplot(level = NULL, size = 1.5) +
  autolayer (vic_births |> tail(n = 36), Births, colour = "black") +
  guides(color = "none")
ggsave("VicBirthsForecast.png")  


vic_births_models |> augment() -> vic_births_augmented
vic_births_augmented

vic_births_augmented |> filter(.model == "mean") |> tail(n = 12) |>
  ggplot(mapping = aes(x = Month)) +
  geom_line(mapping = aes(y = Births, color = "Data"), size = 1) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted"), size = 1) + 
  geom_point(mapping = aes(y = Births)) + 
  geom_point(mapping = aes(y = .fitted))
ggsave("VicBirthsFittedMean.png")  

vic_births_augmented |> filter(.model == "naive") |> tail(n = 12) |>
  ggplot(mapping = aes(x = Month)) +
  geom_line(mapping = aes(y = Births, color = "Data"), size = 1) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted"), size = 1) + 
  geom_point(mapping = aes(y = Births)) + 
  geom_point(mapping = aes(y = .fitted))
ggsave("VicBirthsFittedNaive.png")  

vic_births_augmented |> filter(.model == "drift") |> tail(n = 12) |>
  ggplot(mapping = aes(x = Month)) +
  geom_line(mapping = aes(y = Births, color = "Data"), size = 1) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted"), size = 1) + 
  geom_point(mapping = aes(y = Births)) + 
  geom_point(mapping = aes(y = .fitted))
ggsave("VicBirthsFittedDrift.png")  

vic_births_models |> select(drift) |> gg_tsresiduals()
p <- vic_births_models |> select(drift) |> gg_tsresiduals()
ggsave("VicBirthsResidDrift.png", plot = p)


vic_births_models |> select(mean) |> gg_tsresiduals()
p <- vic_births_models |> select(mean) |> gg_tsresiduals()
ggsave("VicBirthsResidMean.png", plot = p)


vic_births_models |> select(mean) |> augment() |>
  features(.innov, ljung_box, lag = 10)

#prediction intervals
vic_births_forecast
vic_births_forecast |> 
  filter(.model == "mean") |> 
  autoplot(size = 1.5) +
  autolayer (vic_births |> tail(n = 36), Births, colour = "black")
  
vic_births_forecast |> 
  filter(.model == "naive") |> 
  autoplot(size = 1.5) +
  autolayer (vic_births |> tail(n = 36), Births, colour = "black")

vic_births_forecast |>
  hilo() 

google2015Data |>
  model(NAIVE(Close)) |>
  forecast(h = 10) |>
  hilo()

google2015Data |>
  model(NAIVE(Close)) |>
  forecast(h = 10) |>
  hilo(level = 99)

google2015Data |>
  model(NAIVE(Close)) |>
  forecast(h = 10) |>
  autoplot(level = c(50, 99))

ggsave("Google2015ConfInt.png")

vic_births_forecast |> 
  filter(.model == "mean") |>
  autoplot(level = c(50, 99))
ggsave("VicBirthMeanConfInt.png")


vic_births_forecast |> 
  filter(.model == "naive") |>
  autoplot(level = c(50, 99))
ggsave("VicBirthNaiveConfInt.png")


vic_births_forecast |> 
  filter(.model == "drift") |>
  autoplot(level = c(50, 99))
ggsave("VicBirthDriftConfInt.png")

vic_births_forecast |> 
  filter(.model == "s_naive") |>
  autoplot(level = c(50, 99))
ggsave("VicBirthSNaiveConfInt.png")


antidiabetic <- PBS |> 
  filter(ATC2 == "A10") |>
  select(Month, Concession, Type, Cost) |>
  summarize(TotalCost = sum(Cost)) |>
  mutate(Cost = TotalCost / 1000000) #just to have smaller values
antidiabetic |> autoplot(Cost) 
ggsave("A10Plot.png")

antidiabetic |>
  model(naive = NAIVE(Cost)) |> 
  forecast(h = 24) -> antiDForecast

antiDForecast |> 
  autoplot(level = 95) + 
  autolayer(antidiabetic, Cost)
ggsave("AntidiabeticConfInt.png")

antiDForecast |> hilo()

antidiabetic |>
  model(naive = NAIVE(log(Cost))) |> 
  forecast(h= 24) -> antiDLogForecast

antiDLogForecast

antidiabetic |> 
  model(naive = NAIVE(log(Cost))) |> 
  augment()

antiDLogForecast |> hilo() |> print(n = 24)


antiDLogForecast |> 
  autoplot(level = 95) + 
  autolayer(antidiabetic, Cost) 
ggsave("AntidiabeticLogConfInt.png")


antidiabetic |> features(Cost, guerrero)
antidiabetic |>
  model(naive = NAIVE(box_cox(Cost, lambda = 0.13))) |> 
  forecast(h= 24) -> antiDBCForecast
antiDBCForecast |> hilo() |> print(n = 24)
antiDBCForecast |> 
  autoplot(level = 95) + 
  autolayer(antidiabetic, Cost) 
ggsave("AntidiabeticBoxCoxConfInt.png")

us_retail_employment <- us_employment |>
  filter(year(Month)>= 1990, Title == "Retail Trade") |>
  select(Month, Employed)

us_retail_employment
us_retail_employment |> autoplot() + geom_point()
ggsave("RetailEmploymentPLot.png")
dcmp <- us_retail_employment |>
  model(STL(Employed ~ trend(window = 7), robust = TRUE)) |>
  components()

dcmp |> autoplot() 
ggsave("RetailEmploymentSTL.png")

dcmp |>
  select(-.model) |> #should not have attribute called .model 
  model(NAIVE(season_adjust)) |>
  forecast(h = 24) -> dcmpForecast

dcmpForecast |> 
  autoplot() + 
  autolayer(dcmp, season_adjust)
ggsave("RetailEmploymentSadjustForecast.png")


forecast_dcmp <- us_retail_employment |>
  model(stlf = decomposition_model(STL(Employed ~trend(window = 7), robust = TRUE),
                                   NAIVE(season_adjust),
                                   SNAIVE(season_year ~ lag("year"))))
forecast_dcmp
forecast_dcmp |>
  forecast(h = 24) -> dcmp2Forecast

dcmp2Forecast

dcmp2Forecast |> 
  autoplot(size = 1.5) + 
  autolayer(us_retail_employment, Employed, size = 1.5) 
ggsave("RetailEmploymentForecast.png")


forecast_dcmp |> gg_tsresiduals() 
p <- forecast_dcmp |> gg_tsresiduals() 
ggsave("RetailEmploymentREsidDiag.png", plot = p)


forecast_dcmp2 <- us_retail_employment |>
  model(stlf = decomposition_model(STL(Employed ~trend(window = 7), robust = TRUE),
                                   RW(trend ~ drift()),
                                   NAIVE(remainder),
                                   SNAIVE(season_year ~ lag("year"))))
forecast_dcmp2 |>
  forecast(h = 24) -> dcmp2Forecast2
dcmp2Forecast2
dcmp2Forecast2 |> 
  autoplot(size = 1.5) + 
  autolayer(us_retail_employment, Employed, size = 1.5)
ggsave("REtailEmploymentForecast3Methods.png")

forecast_dcmp2 |> gg_tsresiduals()
p <-forecast_dcmp2 |> gg_tsresiduals()
ggsave("RetailEmploymentREsidDiag3Models.png", plot = p)


#train - test split
aus_beer <- aus_production |> select(Beer)
aus_beer
aus_beer |> 
  filter(year(Quarter) < 1995) 
aus_beer |> 
  filter(year(Quarter) >= 1995)

aus_beer |> slice(0:100)
aus_beer |> slice(-1)
aus_beer |> slice(n())
aus_beer |> slice(5: n())
aus_beer |> slice(n()-19: 0)

trainSize <- dim(aus_beer)[1] * 0.8
testSize <- dim(aus_beer)[1] * 0.2
trainData <- aus_beer |> head(trainSize)
testData <- aus_beer |> tail(testSize)
trainData |> tail()
testData


allData <- aus_beer |>
  filter(year(Quarter) >= 1992)
trainData <- allData |>
  filter(year(Quarter) <= 2007)
testData <- allData |>
  filter(year(Quarter) > 2007)

beer_models <- trainData |>
  model(Mean = MEAN(Beer), 
        Naive = NAIVE(Beer),
        snaive = SNAIVE(Beer ~ lag(4)),
        drift = RW(Beer ~drift()))

accuracy(beer_models) |> 
  arrange(.model) |>
  select(.model, .type, RMSE, MAE, MAPE, MASE, RMSSE)

beer_forecast <- beer_models |> forecast(h = 10)

beer_forecast |>
  autoplot(allData, level = NULL, size = 1.5) +
  guides(colous = guide_legend(title=  "Forecast")) 
ggsave("BeerForecasts.png")

beer_models[1] |> gg_tsresiduals() ->p
ggsave("BeerModelsMeanRedisDiag.png", plot = p)

beer_models[2] |> gg_tsresiduals() ->p
ggsave("BeerModelsNaiveRedisDiag.png", plot = p)

beer_models[3] |> gg_tsresiduals() -> p
ggsave("BeerModelsSNaiveResidDiag.png", plot = p)

beer_models[3] |>  augment() |>
  features(.innov, ljung_box, lag = 8)

beer_models[4] |> gg_tsresiduals() ->p
ggsave("BeerModelsDriftResidDiag.png", plot = p)


accuracy(beer_forecast, testData) |>
  arrange(.model) |>
  select(.model, .type, RMSE, MAE, MAPE, MASE, RMSSE)

accuracy(beer_forecast, allData) |>
  arrange(.model) |>
  select(.model, .type, RMSE, MAE, MAPE, MASE, RMSSE)

fb_stock <- gafa_stock |>
  filter(Symbol == "FB") |>
  mutate(trading_day = row_number()) |>
  update_tsibble(index = trading_day, regular = TRUE)
fb_stock
fb_stock |> autoplot(Close)
ggsave("FBPlot.png")

fb_stretch <- fb_stock |>
  stretch_tsibble(.init = 3, .step = 1)

fb_stretch |>
  select(Date, Close, trading_day, .id) -> fb_stretch

fb_stretch

fit_cv <- fb_stretch |> 
  model(RW(Close ~ drift()))

fit_cv
fc_cv <- fit_cv |>
  forecast(h = 1)

fc_cv

fc_cv |> accuracy(fb_stock) |> 
  select(.model, .type, RMSE, MAE, MAPE, MASE, RMSSE)

fb_stock |>
  model(RW(Close ~ drift())) |>
  accuracy() |>
  select(.model, .type, RMSE, MAE, MAPE, MASE, RMSSE)

#regression
us_change

us_change |>
  pivot_longer(c(Consumption, Income), names_to = "Series") |>
  autoplot(value) 

ggsave("UsChange.png")


us_change |>
  ggplot(mapping = aes(x = Income, y = Consumption)) +
  geom_point() +
  geom_smooth(method = "lm", se = FALSE)    
ggsave("UsChangeScatter.png")


us_change |>
  model(TSLM(Consumption ~ Income)) |> #notation means: build model to predict Consumption using Income as predictor
  report()

us_change |>
  model(TSLM(Consumption ~ Income + Savings)) |> report()

us_change |>
  pivot_longer(-Quarter, names_to = "Name") -> us_change_long

us_change_long |>
  ggplot(mapping = aes(x = Quarter, y = value, color = Name)) +
  geom_line() +
  facet_grid(vars(Name), scales = "free_y") +
  guides (colour = "none") 

us_change |>
  GGally::ggpairs(columns = 2:6) 


us_change |> 
  model(TSLM(Consumption ~ Income + Savings + Unemployment + Production)) |> 
  augment() |>
  ggplot(mapping = aes(x = Quarter)) +
  geom_line(mapping = aes(y = Consumption, color = "Data")) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted")) +
  guides(color = guide_legend(title = NULL))

us_change |>
  model(TSLM(Consumption ~ Income + Savings + Unemployment + Production)) |> 
  augment() |> 
  ggplot(mapping = aes(x = Consumption, y = .fitted)) +
  geom_point() +
  geom_abline(intercept = 0, slope = 1) 

residuals <- us_change |>
  model(all = TSLM(Consumption ~ Income + Savings + Unemployment + Production)) |>
  augment()

us_change |>
  left_join(residuals, by = "Quarter") |>
  pivot_longer(c(Income, Production, Savings, Unemployment), names_to = "predictor", values_to = "x") |>
  ggplot(mapping = aes(x = x, y = .resid)) +
  geom_point() +
  facet_wrap(vars(predictor), scales = "free") 

residuals |>
  ggplot(mapping = aes(x = .fitted, y = .resid)) +
  geom_point() 
