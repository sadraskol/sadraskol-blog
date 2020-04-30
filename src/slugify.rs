pub fn slugify(string: String) -> String {
    let string: String = unidecode::unidecode(string.as_str())
        .to_lowercase()
        .trim_matches(|c: char| c == '-' || c.is_whitespace())
        .replace(' ', "-");

    let mut slug = Vec::with_capacity(string.len());

    let mut is_sep = true;

    for x in string.chars() {
        match x {
            'a'..='z' | '0'..='9' => {
                is_sep = false;
                slug.push(x as u8);
            }
            _ => {
                if !is_sep {
                    is_sep = true;
                    slug.push(b'-');
                } else {
                }
            }
        }
    }

    if slug.last() == Some(&(b'-')) {
        slug.pop();
    }

    String::from_utf8(slug).unwrap()
}

#[cfg(test)]
mod test {
    use crate::slugify::slugify;

    #[test]
    fn all_slugify_known_cases() {
        assert_eq!(
            "super-and-the-elephant".to_string(),
            slugify("Super and the elephant".to_string())
        );
        assert_eq!(
            "ode-a-l-esperluette".to_string(),
            slugify("Ode à l'esperluette".to_string())
        );
        assert_eq!(
            "l-ethique-liberale-et-l-esprit-de-l-agile".to_string(),
            slugify("L'éthique libérale et l'esprit de l'Agile".to_string())
        );
        assert_eq!(
            "l-argument-ontologique-de-l-agilite".to_string(),
            slugify("L'argument ontologique de l'agilité".to_string())
        );
        assert_eq!(
            "pourquoi-software-machiavel".to_string(),
            slugify("Pourquoi Software & Machiavel ?".to_string())
        );
        assert_eq!(
            "kafka-n-est-pas-kafkaien".to_string(),
            slugify("Kafka n'est pas kafkaïen".to_string())
        );
        assert_eq!(
            "if-less-game-of-life".to_string(),
            slugify("If-less game of life".to_string())
        );
        assert_eq!(
            "developer-s-proust-questionnaire".to_string(),
            slugify("Developer's Proust Questionnaire".to_string())
        );
        assert_eq!(
            "elixir-phoenix-framework-tips".to_string(),
            slugify("Elixir & phoenix framework tips".to_string())
        );
        assert_eq!(
            "experimenting-pushstate-to-boost-page-loading".to_string(),
            slugify("Experimenting pushstate to boost page loading".to_string())
        );
        assert_eq!(
            "press-review-4".to_string(),
            slugify("Press review #4".to_string())
        );
        assert_eq!(
            "quick-introduction-to-macro-in-elixir".to_string(),
            slugify("Quick introduction to macro in Elixir".to_string())
        );
        assert_eq!(
            "press-review-1".to_string(),
            slugify("Press review #1".to_string())
        );
        assert_eq!(
            "the-alien-erlang-syntax-choices".to_string(),
            slugify("The alien erlang syntax choices".to_string())
        );
        assert_eq!(
            "press-review-2".to_string(),
            slugify("Press review #2".to_string())
        );
        assert_eq!(
            "press-review-3".to_string(),
            slugify("Press review #3".to_string())
        );
        assert_eq!(
            "why-null-leads-to-bad-implementations".to_string(),
            slugify("Why null leads to bad implementations".to_string())
        );
        assert_eq!(
            "the-survival-kit-for-functional-language-beginner".to_string(),
            slugify("The survival kit for functional language beginner".to_string())
        );
        assert_eq!(
            "how-to-create-a-bash-auto-complete".to_string(),
            slugify("How to create a bash auto complete".to_string())
        );
        assert_eq!(
            "composition-with-functional-programming".to_string(),
            slugify("Composition with functional programming".to_string())
        );
        assert_eq!(
            "digging-in-the-depth-of-fibonacci".to_string(),
            slugify("Digging in the depth of Fibonacci".to_string())
        );
        assert_eq!(
            "simple-take-on-monadic-types-the-maybe".to_string(),
            slugify("Simple take on monadic types: the Maybe".to_string())
        );
        assert_eq!(
            "the-listzipper-applications-comonads-in-the-wild".to_string(),
            slugify("The ListZipper applications: Comonads in the wild".to_string())
        );
        assert_eq!(
            "l-inefficacite-de-la-critique-de-l-agile-par-foucault".to_string(),
            slugify("L'inefficacité de la critique de l'Agile par Foucault".to_string())
        );
        assert_eq!(
            "press-review-5".to_string(),
            slugify("Press review #5".to_string())
        );
        assert_eq!(
            "common-pattern-for-bash-auto-complete".to_string(),
            slugify("Common pattern for bash auto complete".to_string())
        );
        assert_eq!(
            "my-experience-with-purescript-so-far".to_string(),
            slugify("My experience with Purescript so far".to_string())
        );
        assert_eq!(
            "response-to-vjeux-article-on-ocaml".to_string(),
            slugify("Response to Vjeux article on Ocaml".to_string())
        );
        assert_eq!(
            "happy-new-year-of-code".to_string(),
            slugify("Happy new year of code".to_string())
        );
        assert_eq!(
            "simple-take-on-monadic-types-the-list".to_string(),
            slugify("Simple take on monadic types : the List".to_string())
        );
        assert_eq!(
            "les-types-algebriques-pour-les-langages-orientes-objet".to_string(),
            slugify("Les types algébriques pour les langages orientés objet".to_string())
        );
        assert_eq!(
            "revue-de-presse-special-parcoursup".to_string(),
            slugify("Revue de presse : spécial parcoursup".to_string())
        );
        assert_eq!(
            "unexpected-values-in-java".to_string(),
            slugify("Unexpected values in Java".to_string())
        );
    }
}
