import json
import random

def clear_console():
    import os
    os.system('cls' if os.name == 'nt' else 'clear')

quiz_1: str = "quiz.json"
quiz_2: str = "partial2.json"

with open(quiz_2, "r") as file:
    json_quiz: dict = json.load(file)
    length: int = len(json_quiz)
    running: bool = True
    asked = set()
    correct_answers: int = 0
    wrong: int = 0
    while running:
        if len(asked) == length:
            asked.clear()
            correct_answers = 0
            wrong = 0
        idx = str(random.randint(1, length))
        while idx in asked:
            idx = str(random.randint(1, length))
        asked.add(idx)
        print(f"Correct: {correct_answers}")
        print(f"Wrong: {wrong}")
        print(f'{len(asked)}/{length}')
        q = json_quiz[idx]
        text = q['question']
        answers = [v for k, v in q.items() if k not in ['question', 'correct']]
        correct = q['correct']
        print(text)
        for index, answer in enumerate(answers):
            letter = chr(65 + index)
            print(f"{letter}. {answer}")
        user_input = input("Your answer(separate by comma if multiple): ").split(',')
        if set(user_input) == set(correct):
            correct_answers += 1
            print("\033[32mCorrect answer!\033[0m")
        else:
            wrong += 1
            print("\033[31mWrong answer\033[0m")
            print("Correct answers: ", correct)

