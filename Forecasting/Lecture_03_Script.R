library(tidyverse)
library(fpp3)
library(fma)

#time series plot
olympic_running |> autoplot()

olympic_running |>
  filter(Length == 100 & Sex == "men") |>
  autoplot()


?PBS 
PBS |> view()
PBS

PBS |> distinct(ATC1_desc, ATC1)

PBS |>
  filter(ATC1_desc == "Nervous system") |>
  distinct(ATC2_desc)

PBS |>
  distinct(ATC2_desc, ATC2) |>
  print(n = 85)

#antidiabetic drugs
A10 <- PBS |>
  filter(ATC2 == "A10")

A10 
A10 |> distinct(ATC1)
A10 |> distinct(Concession)
A10 |> distinct(Type)

A10 <- A10 |> 
  select(Month, Concession, Type, Cost) |>
  summarize(TotalCost = sum(Cost)) |>
  mutate(Cost = TotalCost / 1000000)

A10
A10 |> autoplot()

#vitamins
A11 <- PBS |>
  filter(ATC2 == "A11") |>
  select(Month, Concession, Type, Cost) |>
  summarize(TotalCost = sum(Cost)) |>
  mutate(Cost = TotalCost / 1000000)

A11 |> autoplot()  

#mineral supplements
A12 <- PBS |>
  filter(ATC2 == "A12") |>
  select(Month, Concession, Type, Cost) |>
  summarize(TotalCost = sum(Cost)) |>
  mutate(Cost = TotalCost / 1000000)

A12 |> autoplot()

#vaccines
J07 <- PBS |>
  filter(ATC2 == "J07") |>
  select(Month, Concession, Type, Cost) |>
  summarize(TotalCost = sum(Cost)) |>
  mutate(Cost = TotalCost / 1000000)

J07 |> autoplot()

#Analgesics
N02 <- PBS |>
  filter(ATC2 == "N02") |>
  select(Month, Concession, Type, Cost) |>
  summarize(TotalCost = sum(Cost)) |>
  mutate(Cost = TotalCost / 1000000)

N02 |> autoplot()


A10 |> autoplot(TotalCost) +
  labs(x = "Month", y = "Million $", title = "Antidiabetic drug sales")
ggsave("Antidiabetics.png")

A10 |> autoplot(TotalCost) +
  geom_point() +
  labs(x = "Month", y = "Million $", title = "Antidiabetic drug sales")
ggsave("AntidiabeticsPoint.png")



A10 |>
  head(n = 35) |>
  autoplot() +
  geom_point()

unitroot_ndiffs(A10$Cost)


A10 |> autoplot(TotalCost) +
  geom_point() +
  labs(title = "Antidiabetic drugs")
ggsave("Plot_A10.png")

A11 |> autoplot(TotalCost) +
  geom_point() +
  labs(title = "Vitamins")
ggsave("Plot_A11.png")

A12 |> autoplot(TotalCost) +
  geom_point() +
  labs(title = "Mineral supplements")
ggsave("Plot_A12.png")

A12 |> tail(n = 35) |> view()

N02|> autoplot(TotalCost) +
  geom_point() +
  labs(title = "Analgesics")
ggsave("Plot_N02.png")


?AirPassengers
AirPassengers 

AirPassengers |>
  as_tsibble() |>
  autoplot() +
  geom_point() +
  labs(title = "Airline passengers")
ggsave("Plot_Airline.png")

EuStockMarkets
?EuStockMarkets

EuStockMarkets |>
  as_tsibble()

EuStockMarkets |>
  as_tsibble() |>
  filter(key == "DAX") |>
  autoplot(value) +
  labs(Title = "Dax Stock index")

aus_production
?aus_production

aus_bricks <- aus_production |>
  select(Bricks)

aus_bricks |>
  autoplot() +
  geom_point() +
  labs(title = "Australian bricks production")
ggsave("Plot_Bricks.png")

lynx
?lynx
lynx |>
  autoplot() +
  geom_point() +
  labs(title = "Lynx trappings")
ggsave("Plot_Lynx.png")

?vic_elec
vic_elec |>
  autoplot(Demand) +
  labs(title = "Electricity demand")

#half-hour data. One day has 48 observations, one week has 336 observations, one year has 17520 observations
vic_elec |>
  head(n = 17520) |>
  autoplot(Demand) +
  labs(title = "Electricity demand for first year")

vic_elec |>
  head(n =1344) |>
  autoplot(Demand) +
  labs(title = "Electricty demand for 4 weeks")

vic_elec |>
  slice(700:2400) |>
  autoplot(Demand)

vic_elec |>
  head(n = 336) |>
  autoplot() +
  geom_point() +
  labs(title = "Electricity demand for 1 week")

ustreas
?ustreas
ustreas |> 
  autoplot() +
  geom_point() +
  labs(title = "Us treasury bill contracts")

gafa_stock 
?gafa_stock

gafa_stock |> distinct(Symbol)

apple <- gafa_stock |>
  filter(Symbol == "AAPL")

apple |> autoplot(difference(Close))
ggsave("Plot_AppleDiff.png")

#seasonal plots

A10 |> autoplot()
A10 |> gg_season(TotalCost)

AirPassengers |> autoplot()
AirPassengers |> 
  as_tsibble() |>
  gg_season(value, labels = "left", period = 12)


vic_elec |>
  autoplot(Demand)

vic_elec |>
  gg_season(Demand)

vic_elec |>
  gg_season(Demand, period = "month")

vic_elec |>
  gg_season(Demand, period = "week")

vic_elec |>
  gg_season(Demand, period = "day")

vic_elec |>
  gg_season(Demand, period = "day", facet_period = "year")


aus_bricks |>
  gg_season()


#not seasonal data
lynx |>
  as_tsibble() |>
  gg_season()

?gg_season

ustreas
ustreas |> as_tsibble() -> ustreasTsibble

ustreasTsibble
days <- seq(as.Date("1981-01-01"), by = "day", length = 100)
days
ustreasTsibble  <- tsibble(
  Date = days,
  Values = ustreas,
  index = Date
)
ustreasTsibble
ustreasTsibble |> autoplot()

ustreasTsibble |>
  gg_season()

ustreasTsibble |>
  gg_season(period = "week")

ustreasTsibble |>
  gg_season(period = "month")

EuStockMarkets
EuStockMarkets |>
  as_tsibble() |>
  filter(key == "DAX") -> DaxStock


DaxStock
DaxStock |> 
  mutate(Date = as.Date(index)) |>
  update_tsibble(index = Date) |>
  select(Date, value) ->DaxStock

DaxStock
DaxStock |> fill_gaps(.full = TRUE) -> DaxStockNoMissing

DaxStockNoMissing |>
  gg_season(period = 5)

#seasonal subseries plot
A10 |> gg_subseries()
ggsave("A10_Subseasonal.png")

A11 |> gg_subseries()
ggsave("Vitamins_subseasonal.png")

aus_bricks |> gg_subseries()
ggsave("Bricks_Subseasonal.png")

vic_elec |> head(n = 1000) |> gg_subseries(Demand, period = 48)

#scatter plot
vic_elec
vic_elec |> autoplot()

pivot_longer(vic_elec, cols = c("Demand", "Temperature"), names_to= "Attribute", values_to = "Value") -> vic_elec_long

vic_elec_long |> autoplot()

vic_elec_long |> ggplot() +
  geom_line(mapping = aes(x = Date, y = Value)) +
  facet_wrap(vars(Attribute), scales = "free_y", nrow = 2, ncol = 1)
ggsave("Plot_Scatter_VicElec.png")


vic_elec |> ggplot() +
  geom_point(mapping = aes(x = Temperature, y = Demand))
ggsave("Plot_Scatter_VicElec2.png")

vic_elec |> ggplot() +
  geom_point(mapping = aes(x = Temperature, y = Demand, color = Holiday))
ggsave("Plot_Scatter_VicElec3.png")

?cor
cor(vic_elec$Demand, vic_elec$Temperature, method = "spearman")

tourism

visitors <- tourism |>
  group_by(State) |>
  summarize(Trips = sum(Trips))

visitors |> autoplot()
visitors |> ggplot() +
  geom_line(mapping = aes(x = Quarter, y = Trips)) +
  facet_grid(vars(State), scales = "free_y")
ggsave("Plot_visitors.png")

library(GGally)
visitors_wide <- 
  pivot_wider(visitors, values_from= Trips, names_from=State)

ggpairs(visitors_wide, columns = 2:9)
ggsave("PLot_GGPairs.png")


library(reshape)
tips
ggpairs(tips)
ggsave("Plot_Tips_All.png")


ggpairs(tips, columns = c(1,2,4,5,6,7), mapping = aes(color = sex))
ggsave("Plot_Tips2.png")


ggpairs(tips, columns =c(1,2,4,5,6,7), mapping = aes(colour = sex), 
        lower = list(continuous = "smooth", combo = "facetdensity", discrete = "rowbar"))
ggsave("Plot_Tips3.png")


ggpairs(tips, columns =c(1,2,4,5,6,7), 
        lower = list(continuous = "smooth", combo = "facetdensity", discrete = "rowbar", mapping = aes(color = sex)))
ggsave("Plot_Tips4.png")
