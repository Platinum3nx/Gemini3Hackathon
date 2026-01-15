import os
import google.generativeai as genai
from dotenv import load_dotenv

load_dotenv()
api_key = os.environ.get("GEMINI_API_KEY")

if not api_key:
    print("❌ Error: GEMINI_API_KEY not found in .env")
else:
    genai.configure(api_key=api_key)
    print("Searching...")
    for m in genai.list_models():
        if 'gemini-3' in m.name:
            print(f"✅ Found: {m.name}")
