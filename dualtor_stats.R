#!/usr/bin/env Rscript

library(tidyverse)
library(ggplot2)

args <- commandArgs(trailingOnly = TRUE)

data <- read.csv(header = TRUE, sep = ",", file = args[1])

summary = summarise(data,
                    One = mean(one),
                    Both = mean(both),
                    None = mean(none),
                    torA = mean(torA),
                    torB = mean(torB)
)

df <- pivot_longer(summary, cols=1:3, names_to = "Active", values_to = "States")

svg(gsub(".csv$", ".svg", args[1]))

ggplot(df, aes(fill=Active, y=States, x="")) + 
  geom_bar(position="stack", stat="identity") +
  xlab(paste("Samples: ", nrow(data)))
