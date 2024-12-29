library("tidyverse")
library("fpp3")

data()

view(cars)
?cars

view(starwars)
?starwars

view(pedestrian)
?pedestrian


class(cars)
class(pedestrian)
class(starwars)

#observations x attributes
dim(cars)
dim(starwars)
dim(pedestrian)

count(cars)
count(starwars)
count(pedestrian) 

head(cars)
head(starwars, n = 10)
head(pedestrian, n = 30)
print(head(pedestrian, n = 30), n = 30)

tail(cars, n = 3)
tail(starwars)
tail(pedestrian, n = 10)

#data frame
class(cars)
dim(cars)
cars$speed

cars[1,1]
cars[1, ]
cars[, 1] #this returns a series of type "numeric"

getwd() #get working directory
df <- read.csv("Brent Spot Price.csv")
class(df)
class(df$X)

#tibble
class(starwars)
dim(starwars)
head(starwars)
starwars$name
starwars[, 2]
starwars[1, ]
starwars[1, 2]

#get the name of the first character
starwars[1, ]$name
starwars[, 1][1, 1]
starwars[, 1][1, ]


tb <- read_csv("Brent Spot Price.csv")
tb
class(tb)
spec(tb)

tb_df <- as.data.frame(tb)
class(tb_df)
tb_df

df_tb <- as_tibble(df)
df_tb
class(df_tb)

?read_csv
library("readxl")
?read_excel
tb2 <- read_excel("wineE.xlsx")
tb2
class(tb2)

#Tsibble
olympic_running
class(olympic_running)
head(olympic_running)
dim(olympic_running)
olympic_running$Year
olympic_running[, 2]
olympic_running$Length

x <- data.frame(
  a = 2:10,
  b = c('a', 'b','c','d','e','f','g','h','i')
)
x
class(x)

y <- tibble( a = 2:10,
             b = 12:20,
             c = c("a", "b", "c", "d", "e", "f", "g", "h", "i"))
y
class(y)

z <- tsibble(
  Year = 2015:2019,
  Observation = c(11, 52, 31, 76, 12),
  index = Year
)
z
class(z)

w <- tsibble(
  Year = c(2011, 2012, 2013, 2014, 2011, 2012, 2013, 2014), 
  Specializations = c("CS", "CS", "CS", "CS", "DS", "DS", "DS", "DS"), 
  NrStudents = c(20, 25, 30, 35, 23, 32, 19, 34),
  index = Year,
  key = Specializations
)
w

w2 <- tsibble(
  Year = c(2011, 2012, 2013, 2014, 2011, 2012, 2013, 2014, 2011, 2012, 2013, 2014, 2011, 2012, 2013, 2014), 
  Specializations = c("CS", "CS", "CS", "CS", "DS", "DS", "DS", "DS", "CS", "CS", "CS", "CS", "DS", "DS", "DS", "DS"),
  Group = c(1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2,2, 2),
  NrStudents = c(20, 25, 30, 35, 23, 32, 19, 34, 21, 22, 24,32, 33, 31,29, 32),
  index = Year,
  key = c(Specializations, Group)
)
w2

#year quarter
q1 <- yearquarter("2024 Q1")
q1
?yearquarter
q1b <- yearquarter("2024 Q1", fiscal_start = 6)
q1b

q2 <- yearquarter("2024 Quarter 2")
q2
q3 <- yearquarter("2024-04-03")
q3

q4 <- make_yearquarter(year =2014, quarter = 3)
q4

years <- 2010:2019
yearsRep <- rep(years, each = 4)
yearsRep

q <- 1:4
qRep <- rep(q, 10)
qRep

quarters = make_yearquarter(year = yearsRep, quarter = qRep)
quarters

#yearmonth
m1 <- yearmonth("2010 April")
m1
m2 <- yearmonth("2010 07")
m2
m3 <- yearmonth("2010-08-29")
m3
m4 <-yearmonth("October 2010")
m4
m5 <-yearmonth("22-05-2023") #error, "22-05-2023" cannot be expressed as Date type

m5 <-yearmonth("22-05-2023", format="%d-%m-%y") #works  
m5
m6 <- make_yearmonth(year = 2020, month = 11)
m6
m7 <- make_yearmonth(year = rep(2020:2023, each=12), month = rep(1:12, 4)) # a vector of 48 yearmonth objects
m7
m8 <- yearmonth("2020 M06")
m8

#yearweek
w1 <- yearweek("2020 Week4")
w1
w2 <- yearweek("2020 W25")
w2
w3 <- yearweek("2023-10-12")
w3
w4 <- yearweek("2023-10-12", week_start = 7) 
w4
w5 <- yearweek("2023 Wk40")
w5
w6 <- yearweek("2023-02") #02 is for Febr. - will consider the first of Febr.
w6
w7 <- make_yearweek(year = 2022, week = 5)
w7
w8 <- make_yearweek(year = 2022, week = 60) #result will be 2023 Week 8
w8
w9 <- make_yearweek(year = 2020, week = 53) # will be 2020 Week 53
w9
w10 <- make_yearweek(year = 2021, week = 53) # will be 2022 Week 1
w10
is_53weeks(2021) #FALSE
is_53weeks(2020) #TRUE

#as_date, ymd
d1 <- as_date("2023-09-30")  
d1
d2 <-as_date("2023 09 25")
d2
d3 <- ymd("2020-06-15")
d3
d4 <-ymd(20200605)
d4
d5 <- ymd("Date is 2020 12 22")
d5
s1 <- seq(as_date("2020-01-01"), as_date("2020-03-20"), by = "1 day") # a vector of 73 consecutive days
s1
weeks <- seq(as_date("2020-01-01"), as_date("2020-03-20"), by = "1 week") |> yearweek() #12 consecutive weeks
weeks
months <- seq(as_date("2020-01-01"), as_date("2020-06-30"), by = "1 month") |> yearmonth() # 6 consecutive months
months

#as_datetime and ymd_hms
dt1 <- ymd_hms("2023-09-30 01:00:00")
dt1
dt2 <- ymd_hm("2023-09-30 02:50")
dt2
dt3 <- as_datetime("2013-05-25 14:10:00.00")
dt3
hours <- seq(as_datetime("2023-09-30 01:00:00"), as_datetime("2023-10-02 01:00:00"), by = "hour")
hours

hours2 <- seq(as_datetime("2023-09-30 01:00:00"), as_datetime("2023-10-02 01:00:00"), by = "6 hour")
hours2

#transform Brent Spot Price into tsibble
spot <- read_csv("Brent Spot Price.csv")
spot_ts <- tsibble(spot, index = X)
months <- yearmonth(spot$X)
months
spot_ts <- tsibble(
  price = spot$`Brent crude oil spot price, Monthly (dollars per barrel)`,
  months = months,
  index = months
  )
spot_ts


#with mutate
spot_mutate <- mutate(spot, X = yearmonth(X))
spot_mutate
spot_ts2 <- tsibble(spot_mutate, index = X)
spot_ts2

#with piping
read_csv("Brent Spot Price.csv") |>
  mutate(X = yearmonth(X)) |>
  as_tsibble(index = X) -> spot_ts3

spot_ts3

#mutate

read_csv("Brent Spot Price.csv") |>
  mutate(X = yearmonth(X)) |>
  mutate(Price = `Brent crude oil spot price, Monthly (dollars per barrel)`) |>
  as_tsibble(index = X) -> spot_ts3

spot_ts3

#create new column
olympic_running

olympic_running |>
  mutate(AvgTime = (Time / Length)) -> olympic_running_average
olympic_running_average 

#add external column
nr <- 1:312
olympic_running_average |>
  mutate(Nr = nr) -> olympic_running_average2
olympic_running_average2

#select
starwars
#compute BMI (kg /  m^2) and show just that and the name
starwars |> 
  mutate(BMI = (mass / ((height / 100) * (height / 100)))) |>
  select(name, BMI) -> starwarsBMI

starwars |>
  select(-films, -vehicles, -starships)

#distinct

olympic_running |> 
  distinct(Sex)

olympic_running |>
  distinct(Sex, Length)

olympic_running |>
  distinct(Year) |>
  print(n = 31)

#filter
olympic_running |>
  filter(Sex == "women")

olympic_running |>
  filter(Sex == "women", Length == 100)

olympic_running |>
  filter(Sex == "women", Length == 100, is.na(Time) == FALSE)

#which are the distances for which women have an average of 0.13 in any year
olympic_running_average |>
  filter(Sex == "women", AvgTime < 0.13) |> #times less than 15 seconds
  distinct(Length)

olympic_running_average |>
  filter(Sex == "women", AvgTime < 0.13) |> #times less than 15 seconds
  distinct(Year)

#slice
olympic_running

olympic_running |>
  slice(2:25) |>
  print(n = 25)

#unite
olympic_running |>
  unite(Name, Length, Sex, sep = "-") -> olympic_name

olympic_name

olympic_running |>
  unite(Name, Length, Sex, sep = "-", remove = FALSE) -> olympic_name

olympic_name

olympic_name |> 
  as_tsibble(index = Year, key = Name)


#summary
wines <- read_csv("wine.csv")
wines
summary(wines)
summary(wines$Rose)

sum(wines$Total)

#get the sum of Rose wines sold in 1985
wines |> 
  filter(Year == 1985) |>
  select(Rose) |>
  sum()


#autoplot
olympic_running |> 
  autoplot()

#plot only for 100 m men
olympic_running |>
  filter(Sex == "men", Length == 100) |>
  autoplot()

olympic_running_average2 |>
  filter(Sex == "men", Length == 100) |>
  autoplot(AvgTime)

olympic_running |>  
  filter(Sex == "men", Length == 100) |>
  autoplot() + 
  labs(x = "Time", y = "Running time", title = "Running times at the olympic games", subtitle = "100 meters men", caption= "Plot of running times for the 100 meters men at the olympic games from 1896 to 2016")


wines |> 
  autoplot()

wines |> 
  unite(Date, Year, Month, sep = " ") |>
  mutate(Date = yearmonth(Date)) |>
  as_tsibble(index = Date) -> winesTS

winesTS |> 
  autoplot()

winesTS |> 
  autoplot(Rose)

#total consumption for the first two years
winesTS |>
  slice(1:24) |>
  autoplot(Total)

#autolayer
winesTS |> autoplot(Red, color = "blue") +
  autolayer(winesTS, Rose, color = "red") + 
  autolayer(winesTS, Sparkling, color = "green")


#pivot
autoplot(winesTS)
autoplot(olympic_running)

winesTS |>
  pivot_longer(Red, names_to = "Type", values_to = "QuantitySold") -> winesLonger
winesTS
winesLonger

winesTS |>
  pivot_longer(c(Fortified, Drywhite, Sweetwhite, Rose, Red, Sparkling, Total), names_to = "Type", values_to = "QuantitySold") -> winesLong
winesLong

autoplot(winesLong)

olympic_running |>
  pivot_wider(names_from = Sex, values_from = Time)

olympic_running |>
  pivot_wider(names_from = c(Sex), values_from = Time) |>
  pivot_wider(names_from = Length, values_from = c(men, women)) -> olympic_running_wider

olympic_running_wider |> autoplot()

#ggplot
library("palmerpenguins")
penguins |> 
  view()

ggplot(data = penguins)

penguins |> ggplot()

penguins |> 
  ggplot(mapping = aes(x = flipper_length_mm, y = body_mass_g))

penguins |> 
  ggplot(mapping = aes(x = flipper_length_mm, y = body_mass_g)) +
  geom_point()

penguins |> 
  ggplot(mapping = aes(x = flipper_length_mm, y = body_mass_g)) +
  geom_point() +
  labs(title = "Flipper lengths vs. body mass for penguins")

cor(penguins$flipper_length_mm, penguins$body_mass_g)

penguins |>
  filter(is.na(flipper_length_mm) == FALSE & is.na(body_mass_g)==FALSE) -> penguinsNoNA

cor(penguinsNoNA$flipper_length_mm, penguinsNoNA$body_mass_g)

penguins |> 
  distinct(species)

penguins |> 
  distinct(island)

penguins |> 
  ggplot(mapping = aes(x = flipper_length_mm, y = body_mass_g, color = species)) +
  geom_point() +
  labs(title = "Flipper lengths vs. body mass for penguins")

penguinsNoNA |> filter(species == "Adelie") ->penguinsAdelie
penguinsNoNA |> filter(species == "Chinstrap") -> penguinsChinstrap
penguinsNoNA |> filter(species == "Gentoo") -> penguinsGentoo   

cor(penguinsAdelie$flipper_length_mm, penguinsAdelie$body_mass_g)
cor(penguinsChinstrap$flipper_length_mm, penguinsChinstrap$body_mass_g)
cor(penguinsGentoo$flipper_length_mm, penguinsGentoo$body_mass_g)


penguins |> 
  ggplot(mapping = aes(x = flipper_length_mm, y = body_mass_g)) +
  geom_point(mapping = aes(color = species)) +
  geom_smooth(method = "lm") +
  labs(title = "Flipper lengths vs. body mass for penguins")


penguins |> 
  ggplot(mapping = aes(x = flipper_length_mm, y = body_mass_g)) +
  geom_point(mapping = aes(color = species)) +
  geom_smooth(method = "lm", se = FALSE) +
  labs(title = "Flipper lengths vs. body mass for penguins")


penguins |> 
  ggplot(mapping = aes(x = flipper_length_mm, y = body_mass_g)) +
  geom_point(mapping = aes(color = species)) +
  geom_smooth(method = "lm", level = 0.99) +
  labs(title = "Flipper lengths vs. body mass for penguins")

penguins |> 
  ggplot(mapping = aes(x = flipper_length_mm, y = body_mass_g)) +
  geom_point(mapping = aes(color = species)) +
  geom_smooth(method = "lm", level = 0.3) +
  labs(title = "Flipper lengths vs. body mass for penguins")

ggplot(data = penguins, mapping = aes(x = flipper_length_mm, y = body_mass_g, color = species, size = bill_length_mm, alpha = bill_length_mm)) +
  geom_point() +
  labs(title = "Plot of penguin flipper length vs body mass", x = "Flipper length in milimeters", y = "Body mass in grams")

summary(penguins$bill_length_mm)

ggplot(data = penguins, mapping = aes(x = flipper_length_mm, y = body_mass_g, color = species, size = sex)) +
  geom_point() +
  labs(title = "Plot of penguin flipper length vs body mass", x = "Flipper length in milimeters", y = "Body mass in grams")


ggplot(data = penguins, mapping = aes(x = flipper_length_mm, y = body_mass_g, color = species, shape = sex)) +
  geom_point() +
  labs(title = "Plot of penguin flipper length vs body mass", x = "Flipper length in milimeters", y = "Body mass in grams")

ggplot(data = penguins, mapping = aes(x = flipper_length_mm, y = body_mass_g, color = species, shape = island)) +
  geom_point() +
  labs(title = "Plot of penguin flipper length vs body mass", x = "Flipper length in milimeters", y = "Body mass in grams")

ggplot(data = penguins, mapping = aes(x = flipper_length_mm, y = body_mass_g, color = species, shape = island, size=  sex)) +
  geom_point() +
  labs(title = "Plot of penguin flipper length vs body mass", x = "Flipper length in milimeters", y = "Body mass in grams")

ggplot(data = penguins,  mapping = aes(x = flipper_length_mm, y = body_mass_g)) +
  geom_point(shape = "square", color = "tan") +
  labs(title = "Plot of penguin flipper length vs body mass", x = "Flipper length in milimeters", y = "Body mass in grams")

ggplot(data = penguins,  mapping = aes(x = flipper_length_mm, y = body_mass_g)) +
  geom_point(mapping = aes(shape = island), color = "tan") +
  labs(title = "Plot of penguin flipper length vs body mass", x = "Flipper length in milimeters", y = "Body mass in grams")

colors()


ggplot(data = penguins,  mapping = aes(x = flipper_length_mm, y = body_mass_g, color = species)) +
  geom_point( shape = "square") +
  labs(title = "Plot of penguin flipper length vs body mass", x = "Flipper length in milimeters", y = "Body mass in grams") + 
  scale_color_manual(values = c("magenta", "salmon", "tan", "yellow"))


ggplot(data = penguins, mapping = aes(x = flipper_length_mm, y = body_mass_g, color = species, shape = species)) +
  geom_point() +
  facet_wrap(vars(island)) +
  labs(title = "Plot of penguin flipper length vs body mass", x = "Flipper length in milimeters", y = "Body mass in grams")


ggplot(data = penguins, mapping = aes(x = flipper_length_mm, y = body_mass_g, color = sex, shape = sex)) +
  geom_point() +
  facet_wrap(vars(island, species), nrow = 3, ncol = 3) +
  labs(title = "Plot of penguin flipper length vs body mass", x = "Flipper length in milimeters", y = "Body mass in grams")    

ggplot(data = penguins, mapping = aes(x = species)) +
  geom_bar(color = "red") 


ggplot(data = penguins, mapping = aes(x = species)) +
  geom_bar(color = "red", fill = "red")

ggplot(data = penguins, mapping = aes(x = species)) +
  geom_bar(mapping = aes(fill = island)) 

ggplot(data = penguins, mapping = aes(x = species)) +
  geom_bar(mapping = aes(fill = island)) +
  scale_fill_manual(values = c("lightblue", "lightgrey", "tan"))


ggplot(data = penguins, mapping = aes(x = body_mass_g)) +
  geom_histogram()

ggplot(data = penguins, mapping = aes(x = body_mass_g)) +
  geom_histogram(binwidth = 200)
ggsave(filename = "penguin-plot.png")
