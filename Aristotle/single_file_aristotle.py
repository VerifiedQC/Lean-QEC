import asyncio
import aristotlelib
import shutil

with open("Aristotle/apikey.txt", "r", encoding="utf-8") as file:
    api_key = file.read()

aristotlelib.set_api_key(api_key)

file_to_prove = "ATPTest/Aristotle_target.lean"

async def main():
    # Prove a theorem from a Lean file
    solution_path = await aristotlelib.Project.prove_from_file(file_to_prove)
    shutil.move(solution_path, "Aristotle/Solutions/Aristotle_target.lean")
    #print(f"Solution saved to: {solution_path}")
    print(f"Solution saved to: {"Aristotle/Solutions/Aristotle_target.lean"}")

asyncio.run(main())
