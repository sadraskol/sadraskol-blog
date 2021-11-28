use chrono::{DateTime, Utc};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Date(DateTime<Utc>);

impl Date {
    pub fn parse_from_rfc3339(s: &str) -> Option<Self> {
        DateTime::parse_from_rfc3339(s)
            .ok()
            .map(|d| Date(d.with_timezone(&Utc)))
    }

    pub fn now() -> Self {
        Date(Utc::now())
    }

    pub fn to_rfc3339(&self) -> String {
        self.0.to_rfc3339()
    }

    pub fn human_format(&self, lang: &str) -> String {
        use chrono::Datelike;
        format!(
            "{} {} {}",
            self.0.day(),
            format_month(self.0.month0(), lang),
            self.0.year()
        )
    }
}

fn format_month(month: u32, lang: &str) -> String {
    if lang == "fr" {
        match month {
            0 => "Janvier",
            1 => "Février",
            2 => "Mars",
            3 => "Avril",
            4 => "Mai",
            5 => "Juin",
            6 => "Juillet",
            7 => "Août",
            8 => "Septembre",
            9 => "Octobre",
            10 => "Novembre",
            11 => "Décembre",
            _ => "WHWWW",
        }
        .to_string()
    } else {
        match month {
            0 => "January",
            1 => "February",
            2 => "March",
            3 => "April",
            4 => "May",
            5 => "June",
            6 => "July",
            7 => "August",
            8 => "September",
            9 => "October",
            10 => "November",
            11 => "December",
            _ => "WHWWW",
        }
        .to_string()
    }
}
