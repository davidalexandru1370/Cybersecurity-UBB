from typing import List
import re
import json

with open("quiz.txt", "r") as f:
    lines: List[str] = [line.strip() for line in f.readlines()]
    line_index: int = 0
    n: int = len(lines)
    questions = dict()
    while line_index < n:
        line = lines[line_index]
        question: str = line
        question_index: int = int(re.search('[0-9]+', question).group())
        line_index += 1
        answers: List[str] = []
        while line_index < n and not lines[line_index][0].isdigit():
            answers.append(lines[line_index])
            line_index += 1
        questions[question_index] = {
            'question': question
            } | {answer[0]: answer for answer in answers}
    json: str = json.dumps(questions, indent=4).encode("utf-8").decode("unicode_escape")
    with open("quiz.json", "w", encoding="utf-8") as wf:
        wf.write(json)
