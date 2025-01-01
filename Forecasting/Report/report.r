library(fpp3)
library(tidyverse)
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

ggsave(paste0(folder_path, "/electric_prod.png"), width = 10, height = 6, dpi = 300)