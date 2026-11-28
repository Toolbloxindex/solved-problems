"""Separate occurrence enumeration for the fixed word and its audit controls."""

from itertools import combinations

SOURCE = 'abacadbabdcabcbadac'
NEAR_COVER = 'abacadbcbadac'


def occurrence_unions(source):
    unions = {}
    for length in range(len(source) + 1):
        for image in combinations(range(len(source)), length):
            word = ''.join(source[index] for index in image)
            mask = sum(1 << index for index in image)
            unions[word] = unions.get(word, 0) | mask
    return unions


def covers(source, unions):
    full = (1 << len(source)) - 1
    return {word for word, mask in unions.items() if mask == full}


def project(word, alphabet):
    return ''.join(letter for letter in word if letter in alphabet)


def main():
    full_unions = occurrence_unions(SOURCE)
    examples = {
        SOURCE: {SOURCE},
        'abaca': {'abaca'},
        'bab': {'bab'},
        'cabcba': {'cabcba'},
        'ac': {'ac'},
        'abab': {'ab', 'abab'},
        'ababa': {'aba', 'ababa'},
    }
    for source, expected in examples.items():
        unions = full_unions if source == SOURCE else occurrence_unions(source)
        actual = covers(source, unions)
        assert actual == expected, (source, actual)
        print(f'{source}: {len(unions)} distinct subsequences, covers {sorted(actual)}')

    missing = [index + 1 for index in range(len(SOURCE))
               if not full_unions[NEAR_COVER] & (1 << index)]
    assert missing == [12]
    print(f'{NEAR_COVER} misses {missing}')
    images = (
        (1, 2, 3, 4, 5, 6, 7, 11, 13, 16, 17, 18, 19),
        (1, 2, 3, 4, 5, 6, 9, 14, 15, 16, 17, 18, 19),
        (1, 2, 3, 4, 8, 10, 13, 14, 15, 16, 17, 18, 19),
    )
    for image in images:
        assert image == tuple(sorted(set(image)))
        assert ''.join(SOURCE[index - 1] for index in image) == NEAR_COVER
    assert set().union(*images) == set(range(1, 20)) - {12}

    tests = {}
    for letters in combinations('abcd', 3):
        alphabet = ''.join(letters)
        source = project(SOURCE, alphabet)
        tests[alphabet] = covers(source, occurrence_unions(source))
        assert project(NEAR_COVER, alphabet) in tests[alphabet]
    survivors = [word for word in full_unions if
                 all(project(word, alphabet) in options for alphabet, options in tests.items())]
    assert set(survivors) == {'abcadbcbadac', NEAR_COVER, SOURCE}
    print(f'Survivors of all three-letter projection tests: {sorted(survivors)}')


if __name__ == '__main__':
    main()
